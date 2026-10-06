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
