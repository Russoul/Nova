import SwiftUI

@main
struct PenApp: App {
    var body: some Scene {
        WindowGroup { ContentView() }
    }
}

struct ContentView: View {
    @StateObject private var relay = Relay()
    @StateObject private var editor = Editor()
    @AppStorage("relay") private var address = Bundle.main.object(forInfoDictionaryKey: "NovaPenRelay") as? String ?? "http://127.0.0.1:8765"

    var body: some View {
        VStack(spacing: 0) {
            HStack(spacing: 12) {
                TextField("Relay address", text: $address)
                    .textFieldStyle(.roundedBorder)
                    .textInputAutocapitalization(.never)
                    .autocorrectionDisabled()
                    .frame(maxWidth: 320)
                    .onSubmit { relay.connect(to: address) }
                Button("Connect") { relay.connect(to: address) }
                Divider().frame(height: 24)
                Picker("Tool", selection: $editor.tool) {
                    Image(systemName: "pencil.tip").tag(PenTool.pen)
                    Image(systemName: "eraser").tag(PenTool.eraser)
                    Image(systemName: "lasso").tag(PenTool.lasso)
                    Image(systemName: "arrow.up.and.down.and.arrow.left.and.right").tag(PenTool.move)
                }
                .pickerStyle(.segmented)
                .frame(width: 210)
                Button("Undo", systemImage: "arrow.uturn.backward") { Task { await editor.undo(with: relay) } }
                    .disabled(!editor.canUndo)
                Button("Clear", systemImage: "trash") { editor.clear() }
                    .disabled(editor.isClean || editor.activity != nil)
                Button("Recognise", systemImage: "text.viewfinder") { Task { await editor.recognise(with: relay) } }
                    .disabled(editor.isClean || editor.activity != nil)
                Divider().frame(height: 24)
                Image(systemName: "scribble.variable").foregroundStyle(.secondary)
                Slider(value: $editor.smoothing, in: 0...8)
                    .frame(width: 140)
                    .accessibilityLabel("Smoothing")
                Text(String(format: "%.1f", editor.smoothing))
                    .font(.caption.monospacedDigit())
                    .foregroundStyle(.secondary)
                    .frame(width: 28, alignment: .leading)
                Menu {
                    Toggle("Line numbers", systemImage: "list.number", isOn: $editor.lineNumbers)
                } label: {
                    Label("Options", systemImage: "ellipsis.circle")
                }
                Spacer()
                Text(summary).font(.caption).foregroundStyle(.secondary).lineLimit(1)
            }
            .labelStyle(.iconOnly)
            .padding(8)
            Divider()
            PageRepresentable(editor: editor)
        }
        .onAppear { relay.connect(to: address) }
        .sheet(isPresented: Binding(get: { editor.review != nil }, set: { if !$0 { editor.review = nil } })) {
            ReviewView(editor: editor, relay: relay)
        }
        .alert("Nova Pen", isPresented: Binding(get: { editor.problem != nil }, set: { if !$0 { editor.problem = nil } })) {
            Button("OK") {}
        } message: {
            Text(editor.problem ?? "")
        }
        .onChange(of: relay.version) { sync() }
        .onChange(of: relay.remote) { sync() }
        .onChange(of: editor.isClean) { sync() }
    }

    /// Bring the editor up to the relay's text, but only when clean: a text
    /// that changed on the Mac is taken once no ink is pending over the old one.
    private func sync() {
        guard editor.isClean else { return }
        if editor.version != relay.version { editor.show(relay.lines, tokens: relay.tokens, version: relay.version) }
        if relay.remote != relay.version { Task { await relay.load() } }
        #if DEBUG
        Demo.run(editor, relay)
        #endif
    }

    private var summary: String {
        var parts = [relay.status]
        if let activity = editor.activity { parts.append(activity) }
        if !editor.isClean {
            let spans = editor.requests.reduce(0) { $0 + $1.count }
            parts.append("\(editor.editedRows) rows edited · \(spans) spans · \(editor.requests.count) requests")
        }
        if relay.remote != relay.version { parts.append("changed on the Mac") }
        return parts.joined(separator: " · ")
    }
}

/// The UIKit page in SwiftUI, driven by the editor.
struct PageRepresentable: UIViewRepresentable {
    let editor: Editor

    func makeUIView(context: Context) -> PageScroll {
        let scroll = PageScroll(frame: .zero)
        scroll.addInteraction(UIPencilInteraction(delegate: context.coordinator))
        editor.scroll = scroll
        return scroll
    }

    func updateUIView(_ scroll: PageScroll, context: Context) {}

    func makeCoordinator() -> Coordinator { Coordinator(editor: editor) }

    /// A double tap on the Pencil (or a squeeze) switches pen and eraser.
    final class Coordinator: NSObject, UIPencilInteractionDelegate {
        let editor: Editor
        init(editor: Editor) { self.editor = editor }

        func pencilInteraction(_ interaction: UIPencilInteraction, didReceiveTap tap: UIPencilInteraction.Tap) {
            MainActor.assumeIsolated { editor.tool = editor.tool == .pen ? .eraser : .pen }
        }
    }
}

/// Requests where something did not fit: pick a candidate for each, or none
/// to keep its ink. Apply takes the picks; Keep ink leaves everything as drawn.
struct ReviewView: View {
    @ObservedObject var editor: Editor
    let relay: Relay

    var body: some View {
        NavigationStack {
            List {
                ForEach(Array((editor.review ?? []).enumerated()), id: \.element.id) { i, pending in
                    Section("Lines \(pending.spans[0].first + 1)–\(pending.spans[pending.spans.count - 1].last + 1)") {
                        Text(pending.original.map { $0.joined(separator: "\n") }.joined(separator: "\n⋯\n"))
                            .font(.system(.body, design: .monospaced))
                            .foregroundStyle(.secondary)
                        if let error = pending.error { Text(error).foregroundStyle(.red) }
                        ForEach(Array(pending.candidates.enumerated()), id: \.offset) { k, candidate in
                            Button {
                                editor.review?[i].pick = pending.pick == k ? nil : k
                            } label: {
                                HStack(alignment: .top) {
                                    Image(systemName: pending.pick == k ? "largecircle.fill.circle" : "circle")
                                    VStack(alignment: .leading, spacing: 4) {
                                        Text(candidate.spans.map { $0.joined(separator: "\n") }.joined(separator: "\n⋯\n"))
                                            .font(.system(.body, design: .monospaced))
                                        if !candidate.fits {
                                            Text(objections(candidate)).font(.caption).foregroundStyle(.orange)
                                        }
                                    }
                                }
                            }
                            .buttonStyle(.plain)
                        }
                    }
                }
            }
            .navigationTitle("Review")
            .toolbar {
                ToolbarItem(placement: .cancellationAction) {
                    Button("Keep ink") { editor.review = nil }
                }
                ToolbarItem(placement: .confirmationAction) {
                    Button("Apply") {
                        let pending = editor.review ?? []
                        Task { await editor.apply(pending, with: relay) }
                    }
                }
            }
        }
    }

    private func objections(_ c: Relay.Result.Candidate) -> String {
        (c.new_findings + (c.foreign.isEmpty ? [] : ["not in the specs: " + c.foreign.joined()])).joined(separator: "; ")
    }
}
