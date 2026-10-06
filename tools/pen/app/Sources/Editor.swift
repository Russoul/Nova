import UIKit

/// The editor's state between recognitions: the text (as the relay last gave
/// it) and the marks drawn over it, from which the edited rows, their spans
/// and the requests follow. With no marks the editor is clean: the text alone.
@MainActor
final class Editor: ObservableObject {
    @Published var tool: Mark.Tool = .pen
    @Published private(set) var marks: [Mark] = []
    @Published private(set) var requests: [[Span]] = []

    private(set) var lines: [String] = []
    /// The relay's version of the text shown.
    private(set) var version = ""
    private var layout: Layout?
    private var edited = Set<Int>()
    weak var scroll: PageScroll? {
        didSet {
            scroll?.ink.onMark = { [unowned self] in add($0) }
            scroll?.ink.tool = { [unowned self] in tool }
            if let layout {
                scroll?.show(layout)
                refresh(changed: .null)
            }
        }
    }

    var isClean: Bool { marks.isEmpty }
    var editedRows: Int { edited.count }

    /// New text; shown only when clean, so no marks are lost under it.
    func show(_ lines: [String], version: String) {
        guard isClean else { return }
        self.lines = lines
        self.version = version
        let layout = Layout(rows: lines.map(Array.init), glyphs: .bundled)
        self.layout = layout
        scroll?.show(layout)
        refresh(changed: .null)
    }

    func add(_ mark: Mark) {
        marks.append(mark)
        if let layout { edited.formUnion(layout.rows(editedBy: mark)) }
        refresh(changed: mark.bounds)
    }

    func undo() {
        guard let mark = marks.popLast() else { return }
        edited = Set(marks.flatMap { layout?.rows(editedBy: $0) ?? [] })
        refresh(changed: mark.bounds)
    }

    func clear() {
        let changed = marks.reduce(CGRect.null) { $0.union($1.bounds) }
        marks = []
        edited = []
        refresh(changed: changed)
    }

    private func refresh(changed: CGRect) {
        requests = groupIntoRequests(spans(of: edited), lines: lines)
        scroll?.page.show(marks, changed: changed)
        if let layout { scroll?.ink.show(requests, in: layout) }
    }
}
