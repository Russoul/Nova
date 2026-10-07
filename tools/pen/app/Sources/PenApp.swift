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
    /// The sections panel's width; 0 is closed.
    @AppStorage("sectionsPanel") private var sectionsWidth = 0.0
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
                    Image(systemName: "arrow.uturn.left.circle").tag(PenTool.revert)
                }
                .pickerStyle(.segmented)
                .frame(width: 260)
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
            HStack(spacing: 0) {
                if sectionsWidth > 0 {
                    SectionsPanel(editor: editor)
                        .frame(width: sectionsWidth)
                }
                ResizeHandle(width: $sectionsWidth)
                PageRepresentable(editor: editor)
            }
        }
        .overlay {
            if let palette = editor.palette {
                GeometryReader { geo in
                    let frame = geo.frame(in: .global)
                    ZStack {
                        Color.black.opacity(0.001) // a tap outside closes it
                            .onTapGesture { editor.palette = nil }
                        ToolPalette(selected: editor.tool) { tool in
                            editor.tool = tool
                            editor.palette = nil
                        }
                        .position(ToolPalette.place(palette.at, in: frame))
                    }
                }
                .ignoresSafeArea()
            }
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

    /// A double tap on the Pencil switches pen and eraser; a squeeze opens the
    /// tool palette by the hovering tip, or mid-page when not hovering (unless
    /// the Pencil's settings say a squeeze does nothing).
    final class Coordinator: NSObject, UIPencilInteractionDelegate {
        let editor: Editor
        init(editor: Editor) { self.editor = editor }

        func pencilInteraction(_ interaction: UIPencilInteraction, didReceiveTap tap: UIPencilInteraction.Tap) {
            MainActor.assumeIsolated { editor.tool = editor.tool == .pen ? .eraser : .pen }
        }

        func pencilInteraction(_ interaction: UIPencilInteraction, didReceiveSqueeze squeeze: UIPencilInteraction.Squeeze) {
            MainActor.assumeIsolated {
                guard squeeze.phase == .ended, UIPencilInteraction.preferredSqueezeAction != .ignore else { return }
                if editor.palette != nil {
                    editor.palette = nil
                    return
                }
                let at = squeeze.hoverPose.map { interaction.view?.convert($0.location, to: nil) ?? $0.location }
                editor.palette = Editor.Palette(at: at)
            }
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

/// The tools, in a row that floats over the page; the current one marked.
/// Choosing one closes it.
struct ToolPalette: View {
    let selected: PenTool
    let choose: (PenTool) -> Void

    static let tools: [(PenTool, String)] = [
        (.pen, "pencil.tip"), (.eraser, "eraser"), (.lasso, "lasso"),
        (.move, "arrow.up.and.down.and.arrow.left.and.right"), (.revert, "arrow.uturn.left.circle"),
    ]
    static let size = CGSize(width: 5 * 52 + 16, height: 60)

    var body: some View {
        HStack(spacing: 4) {
            ForEach(Self.tools, id: \.1) { tool, icon in
                Button { choose(tool) } label: {
                    Image(systemName: icon)
                        .font(.title3)
                        .frame(width: 48, height: 48)
                        .background(Circle().fill(tool == selected ? Color.accentColor.opacity(0.25) : .clear))
                        // Lit under a hovering Pencil, as the toolbar's tools are.
                        .contentShape(.hoverEffect, Circle())
                        .hoverEffect(.highlight)
                }
                .buttonStyle(.plain)
            }
        }
        .padding(6)
        .background(.regularMaterial, in: Capsule())
        .shadow(radius: 8, y: 2)
    }

    /// Where the palette's centre goes: a little above the hovering tip, so
    /// the Pencil does not cover it, kept on screen; mid-page without a tip.
    static func place(_ at: CGPoint?, in frame: CGRect) -> CGPoint {
        guard let at else { return CGPoint(x: frame.width / 2, y: frame.height / 2) }
        let half = CGSize(width: size.width / 2 + 12, height: size.height / 2 + 12)
        let x = min(max(at.x - frame.minX, half.width), frame.width - half.width)
        let above = at.y - frame.minY - size.height
        let y = above - half.height < 0 ? at.y - frame.minY + size.height : above
        return CGPoint(x: x, y: min(max(y, half.height), frame.height - half.height))
    }
}

/// The text's sections, by their headings, indented by level; the one the
/// page is showing marked. Choosing one scrolls the page to it.
struct SectionsPanel: View {
    @ObservedObject var editor: Editor

    var body: some View {
        ScrollViewReader { proxy in
            List {
                ForEach(editor.sections.indices, id: \.self) { k in
                    SectionRow(section: editor.sections[k], here: k == editor.currentSection) {
                        editor.jump(to: editor.sections[k])
                    }
                    .id(k)
                }
            }
            .listStyle(.plain)
            .overlay {
                if editor.sections.isEmpty { Text("No headings").foregroundStyle(.secondary) }
            }
            .onChange(of: editor.currentSection) {
                if let k = editor.currentSection { withAnimation { proxy.scrollTo(k, anchor: .center) } }
            }
        }
    }
}

/// The edge between the sections and the page, always there: dragging its
/// grip right opens the panel and widens it as it goes; dragging it left
/// narrows it, and closes it below the narrowest a panel may be.
struct ResizeHandle: View {
    @Binding var width: Double
    @State private var start: Double?
    /// While dragged: whether letting go now would leave the panel closed.
    @State private var closing = false
    /// Whether the Pencil (or a pointer) hovers over the edge.
    @State private var hovering = false
    static let narrowest = 160.0, widest = 640.0

    var body: some View {
        let held = start != nil
        ZStack {
            Rectangle()
                .fill(held && !closing ? Color.accentColor : Color(uiColor: .separator))
                .frame(width: held ? 2 : 1)
            Capsule()
                .fill(held ? (closing ? Color(uiColor: .systemGray) : Color.accentColor)
                           : hovering ? Color.accentColor.opacity(0.45) : Color(uiColor: .systemGray3))
                .frame(width: held ? 12 : hovering ? 10 : 8, height: held ? 76 : hovering ? 64 : 56)
                .overlay {
                    if held && closing {
                        Image(systemName: "xmark").font(.system(size: 8, weight: .bold)).foregroundStyle(.white)
                    }
                }
                .shadow(color: .black.opacity(held ? 0.25 : 0), radius: 4)
        }
        .frame(width: 20)
        .contentShape(Rectangle())
        // Hover drawn by the grip itself, not the system's hover effect: that
        // stays where it was drawn when the grip is dragged away.
        .onHover { hovering = $0 }
        .animation(.easeOut(duration: 0.15), value: hovering)
        .animation(.easeOut(duration: 0.15), value: held)
        .animation(.easeOut(duration: 0.15), value: closing)
        .gesture(DragGesture(minimumDistance: 0, coordinateSpace: .global)
            .onChanged { drag in
                let from = start ?? width
                start = from
                let wanted = from + drag.translation.width
                closing = wanted < Self.narrowest
                width = closing ? 0 : min(wanted, Self.widest)
            }
            .onEnded { _ in
                start = nil
                closing = false
            })
    }
}

/// One heading in the sections panel.
struct SectionRow: View {
    let section: Heading
    let here: Bool
    let jump: () -> Void

    var body: some View {
        Button(action: jump) {
            Text(section.title)
                .font(section.level == 1 ? .headline : .subheadline)
                .foregroundStyle(here ? Color.accentColor : Color.primary)
                .lineLimit(2)
                .padding(.leading, CGFloat(section.level - 1) * 14)
                .frame(maxWidth: .infinity, alignment: .leading)
                .contentShape(Rectangle())
        }
        .buttonStyle(.plain)
        .listRowBackground(here ? Color.accentColor.opacity(0.12) : Color.clear)
    }
}
