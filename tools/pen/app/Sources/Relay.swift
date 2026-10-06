import Foundation

/// The Mac side, tools/pen/relay.py: the file it serves, and a WebSocket that
/// says when the file changes.
@MainActor
final class Relay: ObservableObject {
    @Published private(set) var lines: [String] = []
    @Published private(set) var version = ""
    /// The version the relay last announced; differs from `version` until reloaded.
    @Published private(set) var remote = ""
    @Published private(set) var status = "not connected"

    private var base: URL?
    private var socket: URLSessionWebSocketTask?

    private struct FileReply: Decodable {
        let text: String
        let version: String
    }

    func connect(to address: String) {
        socket?.cancel(with: .goingAway, reason: nil)
        socket = nil
        guard let url = URL(string: address), url.scheme == "http" || url.scheme == "https" else {
            status = "not an http(s) address"
            return
        }
        base = url
        Task {
            await load()
            listen()
        }
    }

    /// The file as the relay has it now.
    func load() async {
        guard let base else { return }
        do {
            let (data, _) = try await URLSession.shared.data(from: base.appending(path: "file"))
            let reply = try JSONDecoder().decode(FileReply.self, from: data)
            var lines = reply.text.components(separatedBy: "\n")
            if reply.text.hasSuffix("\n") { lines.removeLast() }
            self.lines = lines
            version = reply.version
            remote = reply.version
            status = "\(lines.count) lines · \(reply.version.prefix(8))"
        } catch {
            status = "cannot load: \(error.localizedDescription)"
        }
    }

    /// What the relay read in one request: candidates with whether each fits
    /// (adds no checker finding, uses only the specs' characters), and which
    /// one it chose, if any fits.
    struct Result: Decodable {
        struct Candidate: Decodable {
            let spans: [[String]]
            let fits: Bool
            let new_findings: [String]
            let foreign: [String]
        }
        let chosen: Int?
        let candidates: [Candidate]?
        let error: String?
    }

    /// A reply, or word that the file is no longer at the version asked about.
    enum Reply<T> {
        case done(T)
        case stale
    }

    /// Read the requests: each a list of spans with their pictures.
    func recognise(base: String, requests: [[(span: Span, image: Data)]]) async throws -> Reply<[Result]> {
        let body: [String: Any] = ["base": base, "requests": requests.map { request in
            ["spans": request.map { ["first": $0.span.first + 1, "last": $0.span.last + 1,
                                     "image": $0.image.base64EncodedString()] }]
        }]
        let (data, code) = try await post("recognise", body)
        if code == 409 { return .stale }
        struct Reply: Decodable { let results: [Result] }
        return .done(try JSONDecoder().decode(Reply.self, from: data).results)
    }

    /// Make replacements to the file at version `base`, giving `lines`. On
    /// success the relay's text is taken as `lines` at the new version.
    func edit(base: String, _ replacements: [Replacement], giving lines: [String]) async throws -> Reply<String> {
        let body: [String: Any] = ["base": base, "replacements": replacements.map {
            ["first": $0.first + 1, "last": $0.last + 1, "lines": $0.lines]
        }]
        let (data, code) = try await post("edit", body)
        if code == 409 { return .stale }
        guard let reply = try JSONSerialization.jsonObject(with: data) as? [String: Any],
              let version = reply["version"] as? String else { throw URLError(.badServerResponse) }
        self.lines = lines
        self.version = version
        remote = version
        status = "\(lines.count) lines · \(version.prefix(8))"
        return .done(version)
    }

    private func post(_ path: String, _ body: [String: Any]) async throws -> (Data, Int) {
        guard let base else { throw URLError(.badURL) }
        var request = URLRequest(url: base.appending(path: path))
        request.httpMethod = "POST"
        request.timeoutInterval = 300 // a recognition may ask Claude twice
        request.setValue("application/json", forHTTPHeaderField: "Content-Type")
        request.httpBody = try JSONSerialization.data(withJSONObject: body)
        let (data, response) = try await URLSession.shared.data(for: request)
        let status = (response as? HTTPURLResponse)?.statusCode ?? 0
        guard status == 200 || status == 409 else {
            throw NSError(domain: "relay", code: status, userInfo: [NSLocalizedDescriptionKey: String(decoding: data, as: UTF8.self)])
        }
        return (data, status)
    }

    private func listen() {
        guard let base, var url = URLComponents(url: base.appending(path: "events"), resolvingAgainstBaseURL: false)
        else { return }
        url.scheme = url.scheme == "https" ? "wss" : "ws"
        guard let address = url.url else { return }
        let task = URLSession.shared.webSocketTask(with: address)
        socket = task
        task.resume()
        receive(task)
    }

    /// Each notice names the file's version. Reloading is the editor's call:
    /// it reloads only when clean, so no ink is lost under a changed text.
    private func receive(_ task: URLSessionWebSocketTask) {
        task.receive { [weak self] result in
            Task { @MainActor in
                guard let self, self.socket === task else { return }
                switch result {
                case .success(.string(let text)):
                    let notice = try? JSONSerialization.jsonObject(with: Data(text.utf8)) as? [String: String]
                    if let version = notice?["version"] { self.remote = version }
                    self.receive(task)
                case .success:
                    self.receive(task)
                case .failure:
                    self.status = "events lost; retrying"
                    try? await Task.sleep(for: .seconds(2))
                    if self.socket === task { self.listen() }
                }
            }
        }
    }
}
