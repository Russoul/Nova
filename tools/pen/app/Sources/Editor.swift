import UIKit

/// The editor's state: the text (as the relay last gave it) and the marks
/// drawn over it since the last recognition, from which the edited rows,
/// their spans and the requests follow. With no marks the editor is clean:
/// the text alone.
@MainActor
final class Editor: ObservableObject {
    @Published var tool: Mark.Tool = .pen
    @Published private(set) var marks: [Mark] = []
    @Published private(set) var requests: [[Span]] = []
    /// Requests where something did not fit: the user picks, or keeps the ink.
    @Published var review: [Pending]?
    /// What is going on, when something is.
    @Published private(set) var activity: String?
    /// The last thing that went wrong, for the user to see.
    @Published var problem: String?

    /// One request's reading, waiting to be applied.
    struct Pending: Identifiable {
        let id: Int
        let spans: [Span]
        let original: [[String]]
        let candidates: [Relay.Result.Candidate]
        let error: String?
        var pick: Int?
    }

    /// What undo takes back: a stroke, or a recognition (its text edit, and
    /// the marks there were before it).
    private enum Step {
        case mark
        case recognition(undo: [Replacement], marks: [Mark])
    }

    private(set) var lines: [String] = []
    /// The relay's version of the text shown.
    private(set) var version = ""
    private var layout: Layout?
    private var edited = Set<Int>()
    private var steps: [Step] = []
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
    var canUndo: Bool { !steps.isEmpty && activity == nil }
    var editedRows: Int { edited.count }

    /// New text from the relay; shown only when clean, so no marks are lost under it.
    func show(_ lines: [String], version: String) {
        guard isClean else { return }
        steps = []
        take(lines, version: version, marks: [])
    }

    func add(_ mark: Mark) {
        guard activity == nil, review == nil else { return }
        marks.append(mark)
        steps.append(.mark)
        if let layout { edited.formUnion(layout.rows(editedBy: mark)) }
        refresh(changed: mark.bounds)
    }

    func clear() {
        let changed = marks.reduce(CGRect.null) { $0.union($1.bounds) }
        marks = []
        edited = []
        steps.removeAll { if case .mark = $0 { true } else { false } }
        refresh(changed: changed)
    }

    // Recognition ------------------------------------------------------------

    /// Send every request to the relay. If each comes back with a candidate
    /// that fits, apply them all at once; otherwise open the review.
    func recognise(with relay: Relay) async {
        guard let layout, !requests.isEmpty, activity == nil else { return }
        let requests = self.requests
        let payload = requests.map { group in group.compactMap { span in layout.composite(of: span, marks: marks).map { (span, $0) } } }
        activity = "reading \(requests.count) request\(requests.count == 1 ? "" : "s")…"
        let reply: Relay.Reply<[Relay.Result]>
        do {
            reply = try await relay.recognise(base: version, requests: payload)
        } catch {
            activity = nil
            problem = error.localizedDescription
            return
        }
        activity = nil
        switch reply {
        case .stale:
            dropInk()
        case .done(let results):
            let pending = zip(requests, results).enumerated().map { k, pair in
                Pending(id: k, spans: pair.0, original: pair.0.map { Array(lines[$0.first...$0.last]) },
                        candidates: pair.1.candidates ?? [], error: pair.1.error, pick: pair.1.chosen)
            }
            if pending.allSatisfy({ $0.pick != nil }) {
                await apply(pending, with: relay)
            } else {
                review = pending
            }
        }
    }

    /// Apply what was picked. A request with no pick keeps its ink (moved with
    /// the text when lines above it grew or shrank); all other ink goes.
    func apply(_ pending: [Pending], with relay: Relay) async {
        review = nil
        let replacements = pending.filter { $0.pick != nil }.flatMap { p in
            zip(p.spans, p.candidates[p.pick!].spans).map { Replacement(first: $0.first, last: $0.last, lines: $1) }
        }
        guard !replacements.isEmpty, let layout else { return }
        let result = applying(replacements, to: lines)
        let keepRows = Set(pending.filter { $0.pick == nil }.flatMap { $0.spans.flatMap { Array($0.first...$0.last) } })
        activity = "applying…"
        defer { activity = nil }
        do {
            switch try await relay.edit(base: version, replacements, giving: result) {
            case .stale:
                dropInk()
            case .done(let newVersion):
                let kept = marks.compactMap { mark -> Mark? in
                    let rows = layout.rows(editedBy: mark)
                    guard let first = rows.min(), rows.isSubset(of: keepRows) else { return nil }
                    let dy = CGFloat(shift(of: first, by: replacements)) * layout.lineHeight
                    return Mark(tool: mark.tool, points: mark.points.map { CGPoint(x: $0.x, y: $0.y + dy) }, width: mark.width)
                }
                steps = [.recognition(undo: inverse(of: replacements, in: lines), marks: marks)]
                take(result, version: newVersion, marks: kept)
            }
        } catch {
            problem = error.localizedDescription
        }
    }

    /// Undo the last stroke, or the last recognition: its edit is reverted on
    /// the Mac and its ink comes back, to be redrawn.
    func undo(with relay: Relay) async {
        guard let step = steps.last, activity == nil, review == nil else { return }
        switch step {
        case .mark:
            steps.removeLast()
            guard let mark = marks.popLast() else { return }
            edited = Set(marks.flatMap { layout?.rows(editedBy: $0) ?? [] })
            refresh(changed: mark.bounds)
        case .recognition(let undo, let before):
            let restored = applying(undo, to: lines)
            activity = "undoing…"
            defer { activity = nil }
            do {
                switch try await relay.edit(base: version, undo, giving: restored) {
                case .stale:
                    problem = "The file changed on the Mac since; the recognition cannot be undone."
                    steps = []
                case .done(let newVersion):
                    steps.removeLast()
                    take(restored, version: newVersion, marks: before)
                    steps += before.map { _ in .mark }
                }
            } catch {
                problem = error.localizedDescription
            }
        }
    }

    /// The text changed on the Mac under the ink: the ink goes, and the new
    /// text comes in (the view syncs once the editor is clean).
    private func dropInk() {
        problem = "The file changed on the Mac, so the ink was dropped."
        review = nil
        clear()
        steps = []
    }

    // The page ---------------------------------------------------------------

    private func take(_ lines: [String], version: String, marks: [Mark]) {
        self.lines = lines
        self.version = version
        let layout = Layout(rows: lines.map(Array.init), glyphs: .bundled)
        self.layout = layout
        self.marks = marks
        edited = Set(marks.flatMap { layout.rows(editedBy: $0) })
        scroll?.show(layout)
        refresh(changed: marks.reduce(CGRect.null) { $0.union($1.bounds) })
    }

    private func refresh(changed: CGRect) {
        requests = groupIntoRequests(spans(of: edited), lines: lines)
        scroll?.page.show(marks, changed: changed)
        if let layout { scroll?.ink.show(requests, in: layout) }
    }
}
