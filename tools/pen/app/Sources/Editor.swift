import UIKit

/// What the Pencil does: write, erase, lasso characters and ink, move what
/// the lasso took, or revert the lines it traces to the text as it is.
enum PenTool { case pen, eraser, lasso, move, revert }

/// The editor's state: the text (as the relay last gave it) and the marks
/// drawn over it since the last recognition, from which the edited rows,
/// their spans and the requests follow. With no marks the editor is clean:
/// the text alone.
@MainActor
final class Editor: ObservableObject {
    @Published var tool: PenTool = .pen {
        didSet { if tool == .pen || tool == .eraser { select([]) } }
    }
    /// Whether line numbers are shown; remembered. Turning them on or off
    /// moves the text sideways, and every mark with it.
    @Published var lineNumbers: Bool = UserDefaults.standard.bool(forKey: "lineNumbers") {
        didSet {
            UserDefaults.standard.set(lineNumbers, forKey: "lineNumbers")
            if lineNumbers != oldValue { relayout() }
        }
    }
    /// The tool palette, when open: by the hovering Pencil (a point in window
    /// coordinates), or in the middle of the page (nil).
    struct Palette: Equatable { var at: CGPoint? }
    @Published var palette: Palette?
    /// The text's headings, and the one whose section is at the top of the view.
    @Published private(set) var sections: [Heading] = []
    @Published private(set) var currentSection: Int?
    /// How many edited rows each section holds (by index into `sections`).
    @Published private(set) var sectionEdits: [Int: Int] = [:]
    /// The ink being moved: indices into `marks`.
    @Published private(set) var selection: [Int] = []
    /// How many times over a pen stroke is smoothed (0...8); remembered.
    @Published var smoothing: Double = UserDefaults.standard.object(forKey: "smoothing") as? Double ?? Double(defaultSmoothing) {
        didSet { UserDefaults.standard.set(smoothing, forKey: "smoothing") }
    }
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

    /// What undo takes back: a stroke; a lasso or a move (the marks there
    /// were before it); or a recognition (its text edit, and the marks there
    /// were before it).
    private enum Step {
        case mark
        case marks(before: [Mark])
        case recognition(undo: [Replacement], marks: [Mark])
    }

    private(set) var lines: [String] = []
    /// Each line's tokens, for colouring.
    private(set) var tokens: [[Token]] = []
    /// The relay's version of the text shown.
    private(set) var version = ""
    private var layout: Layout?
    private var edited = Set<Int>()
    private var steps: [Step] = []
    weak var scroll: PageScroll? {
        didSet {
            scroll?.ink.onMark = { [unowned self] in add($0) }
            scroll?.ink.tool = { [unowned self] in tool }
            scroll?.ink.smoothing = { [unowned self] in CGFloat(smoothing) }
            scroll?.ink.onLasso = { [unowned self] in lasso($0) }
            scroll?.ink.onRevert = { [unowned self] in revert($0) }
            scroll?.onScroll = { [unowned self] in follow(pageY: $0) }
            scroll?.ink.onMoveBegan = { [unowned self] in beginMove() }
            scroll?.ink.onMove = { [unowned self] in scroll?.ink.showDragged(dragPath, offset: $0) }
            scroll?.ink.onMoveEnded = { [unowned self] in endMove(by: $0) }
            if let layout {
                scroll?.show(layout)
                refresh(changed: .null)
            }
        }
    }

    var isClean: Bool { marks.isEmpty }
    var layoutShown: Layout? { layout }
    var canUndo: Bool { !steps.isEmpty && activity == nil }
    var editedRows: Int { edited.count }

    /// New text from the relay; shown only when clean, so no marks are lost under it.
    func show(_ lines: [String], tokens: [[Token]], version: String) {
        guard isClean else { return }
        steps = []
        take(lines, tokens: tokens, version: version, marks: [])
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
        select([])
        steps.removeAll { if case .recognition = $0 { false } else { true } }
        refresh(changed: changed)
    }

    // Lasso and move ---------------------------------------------------------

    /// A lasso: the characters in it are lifted out of the text (their cells
    /// cleared, their strokes now plain ink), and they and the ink in it are
    /// selected, ready to move.
    func lasso(_ loop: [CGPoint]) {
        guard let layout, activity == nil, review == nil else { return }
        let lifted = Set(marks.compactMap(\.lifted))
        let cells = layout.cells(inside: loop).filter { !lifted.contains($0) }
        let held = marks.indices.filter { marks[$0].tool == .pen && holds(loop, marks[$0]) }
        // Characters the eraser took whole lift nothing.
        let lifts = cells.flatMap { layout.lift($0, under: marks) }
        if !lifts.isEmpty {
            let before = marks
            marks += lifts
            steps.append(.marks(before: before))
            edited = Set(marks.flatMap { layout.rows(editedBy: $0) })
            refresh(changed: lifts.reduce(CGRect.null) { $0.union($1.bounds) })
        }
        let new = marks.indices.suffix(lifts.count).filter { marks[$0].tool == .pen }
        select(held + new)
        if !selection.isEmpty { tool = .move }
    }

    /// Every line a traced path passes through goes back to the text as it
    /// is: its ink, erasures and lifted characters are taken back (edits
    /// reaching into other lines keep their part there), so spans are trimmed,
    /// split, or gone.
    func revert(_ path: [CGPoint]) {
        guard let layout, activity == nil, review == nil else { return }
        let rows = layout.rows(tracedBy: path)
        guard !rows.isDisjoint(with: edited) else { return }
        let before = marks
        marks = layout.reverting(rows, in: marks)
        steps.append(.marks(before: before))
        select([])
        edited = Set(marks.flatMap { layout.rows(editedBy: $0) })
        refresh(changed: (before + marks).reduce(CGRect.null) { $0.union($1.bounds) })
    }

    private func select(_ indices: [Int]) {
        selection = indices
        let box = indices.reduce(CGRect.null) { $0.union(marks[$1].bounds) }
        scroll?.ink.showSelection(box.isNull ? nil : box)
    }

    /// The selected ink as one shape, for drawing it while it moves.
    private var dragPath: CGPath? {
        guard !selection.isEmpty else { return nil }
        let path = CGMutablePath()
        for i in selection {
            let m = marks[i]
            if let ink = m.ink {
                path.addPath(ink)
            } else if let first = m.points.first {
                let line = CGMutablePath()
                line.move(to: first)
                line.addLines(between: m.points.count > 1 ? m.points : [first, first])
                path.addPath(line.copy(strokingWithWidth: m.width, lineCap: .round, lineJoin: .round, miterLimit: 1))
            }
        }
        return path
    }

    /// The selection is lifted off the page, to follow the Pencil.
    private func beginMove() -> Bool {
        guard !selection.isEmpty, activity == nil, review == nil else { return false }
        let picked = Set(selection)
        scroll?.page.show(marks.indices.filter { !picked.contains($0) }.map { marks[$0] },
                          changed: selection.reduce(CGRect.null) { $0.union(marks[$1].bounds) })
        scroll?.ink.showSelection(nil)
        scroll?.ink.showDragged(dragPath, offset: .zero)
        return true
    }

    #if DEBUG
    /// A whole move at once, as a drag with the Pencil would make it.
    func moveSelection(by offset: CGVector) {
        if beginMove() { endMove(by: offset) }
    }
    #endif

    /// The selection is put down where the Pencil let go.
    private func endMove(by offset: CGVector) {
        scroll?.ink.showDragged(nil, offset: .zero)
        guard let layout else { return }
        let before = marks
        if offset != .zero {
            for i in selection { marks[i] = marks[i].moved(dx: offset.dx, dy: offset.dy) }
            steps.append(.marks(before: before))
            edited = Set(marks.flatMap { layout.rows(editedBy: $0) })
        }
        let changed = selection.reduce(CGRect.null) { $0.union(before[$1].bounds).union(marks[$1].bounds) }
        refresh(changed: changed)
        select(selection)
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
            case .done(let (newVersion, newTokens)):
                let kept = marks.compactMap { mark -> Mark? in
                    let rows = layout.rows(editedBy: mark)
                    guard let first = rows.min(), rows.isSubset(of: keepRows) else { return nil }
                    return mark.moved(rows: shift(of: first, by: replacements), lineHeight: layout.lineHeight)
                }
                steps = [.recognition(undo: inverse(of: replacements, in: lines), marks: marks)]
                take(result, tokens: newTokens, version: newVersion, marks: kept, changed: replacements)
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
            select([])
            edited = Set(marks.flatMap { layout?.rows(editedBy: $0) ?? [] })
            refresh(changed: mark.bounds)
        case .marks(let before):
            steps.removeLast()
            let changed = (marks + before).reduce(CGRect.null) { $0.union($1.bounds) }
            marks = before
            select([])
            edited = Set(marks.flatMap { layout?.rows(editedBy: $0) ?? [] })
            refresh(changed: changed)
        case .recognition(let undo, let before):
            let restored = applying(undo, to: lines)
            activity = "undoing…"
            defer { activity = nil }
            do {
                switch try await relay.edit(base: version, undo, giving: restored) {
                case .stale:
                    problem = "The file changed on the Mac since; the recognition cannot be undone."
                    steps = []
                case .done(let (newVersion, newTokens)):
                    steps.removeLast()
                    take(restored, tokens: newTokens, version: newVersion, marks: before, changed: undo)
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

    /// Show new text with these marks. `changed` are the replacements that
    /// made it from the text shown now: then only the rows they touched are
    /// drawn again (all rows below, if the line count changed), with every
    /// row whose tokens changed (the rest of a rule; after a grammar edit,
    /// rows anywhere), and what they changed flashes. Without them the whole
    /// page is drawn again.
    private func take(_ lines: [String], tokens: [[Token]], version: String, marks: [Mark], changed: [Replacement]? = nil) {
        let old = self.lines, oldTokens = self.tokens, oldLayout = layout, oldMarks = self.marks
        self.lines = lines
        self.tokens = tokens
        self.version = version
        let layout = Layout(lines: lines, tokens: tokens, glyphs: .bundled, numbered: lineNumbers)
        self.layout = layout
        self.marks = marks
        sections = headings(of: lines)
        select([])
        edited = Set(marks.flatMap { layout.rows(editedBy: $0) })
        var redraw: [CGRect]?
        if let changed, let first = changed.map(\.first).min() {
            let width = max(layout.size.width, oldLayout?.size.width ?? 0)
            func band(_ rows: Range<Int>) -> CGRect {
                CGRect(x: 0, y: layout.origin(rows.lowerBound, 0).y, width: width, height: CGFloat(rows.count) * layout.lineHeight)
            }
            let edited = changed.contains { $0.growth != 0 }
                ? [band(first..<max(old.count, lines.count))]
                : changed.map { band($0.first..<($0.last + 1)) }
            let moved = movingTokens(oldTokens, after: changed, delta: [:])
            let recoloured = tokens.indices.filter { $0 < moved.count && tokens[$0] != moved[$0] }.map { band($0..<($0 + 1)) }
            redraw = edited + recoloured
        }
        scroll?.show(layout, redraw: redraw)
        refresh(changed: (oldMarks + marks).reduce(CGRect.null) { $0.union($1.bounds) })
        guard let changed else { return }
        var shift = 0, written = [Cell](), removed = [Cell]()
        for r in changed.sorted(by: { $0.first < $1.first }) {
            let top = r.first + shift
            let d = changes(from: Array(old[r.first..<(r.last + 1)]), to: r.lines)
            written += d.written.map { Cell(row: $0.row + top, column: $0.column) }
            removed += d.removed.map { Cell(row: $0.row + top, column: $0.column) }
            shift += r.growth
        }
        scroll?.ink.flash(written: written, removed: removed, in: layout)
    }

    /// The same text laid out again (line numbers shown or hidden): the page
    /// redrawn, and every mark, those kept for undo too, moved with the text.
    private func relayout() {
        guard let old = layout else { return }
        let layout = Layout(lines: lines, tokens: tokens, glyphs: .bundled, numbered: lineNumbers)
        self.layout = layout
        let dx = (layout.gutter - old.gutter) * layout.cellWidth
        func move(_ ms: [Mark]) -> [Mark] { ms.map { $0.moved(dx: dx, dy: 0) } }
        marks = move(marks)
        steps = steps.map {
            switch $0 {
            case .mark: .mark
            case .marks(let before): .marks(before: move(before))
            case .recognition(let undo, let before): .recognition(undo: undo, marks: move(before))
            }
        }
        scroll?.show(layout) // the whole page is drawn again, the moved marks with it
        refresh(changed: .null)
        select(selection)
    }

    /// Scroll so that a section's heading is at the top, a line of room above.
    func jump(to section: Heading) { jump(toRow: section.row) }

    /// Scroll so that a row is near the top, a line of room above, and make
    /// it glow a moment. Its section becomes the current one, even where the
    /// page cannot bring the row to the top (near the end, an earlier line
    /// stays there).
    func jump(toRow row: Int) {
        guard let layout else { return }
        currentSection = sections.lastIndex { $0.row <= row }
        scroll?.scroll(toPageY: layout.origin(max(0, row - 1), 0).y)
        scroll?.ink.glow(CGRect(x: 0, y: layout.origin(row, 0).y, width: layout.size.width, height: layout.lineHeight))
    }

    /// Mark the section the view is in: the last heading at or above its top.
    private func follow(pageY: CGFloat) {
        guard let layout else { return }
        // The row a quarter of a line below the top: a heading just under the
        // top line counts as there, whatever the rounding.
        let top = Int((pageY / layout.lineHeight - Layout.margin + 1.25).rounded(.down))
        let k = sections.lastIndex { $0.row <= top }
        if k != currentSection { currentSection = k }
    }

    private func refresh(changed: CGRect) {
        requests = groupIntoRequests(spans(of: edited), lines: lines)
        let counts = editsBySection(edited, sections)
        if counts != sectionEdits { sectionEdits = counts }
        scroll?.page.show(marks, changed: changed)
        if let layout { scroll?.ink.show(requests, in: layout) }
    }
}
