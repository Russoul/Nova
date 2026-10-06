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
    @AppStorage("relay") private var address = "http://127.0.0.1:8765"

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
                    Image(systemName: "pencil.tip").tag(Mark.Tool.pen)
                    Image(systemName: "eraser").tag(Mark.Tool.eraser)
                }
                .pickerStyle(.segmented)
                .frame(width: 110)
                Button("Undo", systemImage: "arrow.uturn.backward") { editor.undo() }
                    .disabled(editor.isClean)
                Button("Clear", systemImage: "trash") { editor.clear() }
                    .disabled(editor.isClean)
                Spacer()
                Text(summary).font(.caption).foregroundStyle(.secondary).lineLimit(1)
            }
            .labelStyle(.iconOnly)
            .padding(8)
            Divider()
            PageRepresentable(editor: editor)
        }
        .onAppear { relay.connect(to: address) }
        .onChange(of: relay.version) { sync() }
        .onChange(of: relay.remote) { sync() }
        .onChange(of: editor.isClean) { sync() }
    }

    /// Bring the editor up to the relay's text, but only when clean: a text
    /// that changed on the Mac is taken once no ink is pending over the old one.
    private func sync() {
        guard editor.isClean else { return }
        if editor.version != relay.version { editor.show(relay.lines, version: relay.version) }
        if relay.remote != relay.version { Task { await relay.load() } }
    }

    private var summary: String {
        var parts = [relay.status]
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
