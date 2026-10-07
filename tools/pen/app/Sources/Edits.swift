import CoreGraphics

/// One stroke of the Pencil since the last recognition, in page points.
/// Marks apply in order: an eraser clears whatever lies under it, the text's
/// strokes and earlier ink alike; ink drawn after it stays.
struct Mark {
    enum Tool { case pen, eraser }
    let tool: Tool
    let points: [CGPoint]
    let width: CGFloat
    /// A pen stroke's ink, as a shape to fill whose width follows the
    /// Pencil's pressure; without it the stroke is `points` at `width`.
    let ink: CGPath?

    init(tool: Tool, points: [CGPoint], width: CGFloat, ink: CGPath? = nil) {
        self.tool = tool
        self.points = points
        self.width = width
        self.ink = ink
    }

    /// A pen stroke from the Pencil's samples, smoothed.
    init(pen samples: [InkSample]) {
        let track = smoothed(samples)
        self.init(tool: .pen, points: track.map(\.point), width: 2 * (track.map(\.radius).max() ?? 1), ink: inkOutline(track))
    }

    /// The same mark, moved down by dy (when lines above it grew or shrank).
    func moved(by dy: CGFloat) -> Mark {
        var shift = CGAffineTransform(translationX: 0, y: dy)
        return Mark(tool: tool, points: points.map { CGPoint(x: $0.x, y: $0.y + dy) }, width: width,
                    ink: ink.flatMap { $0.copy(using: &shift) })
    }

    var bounds: CGRect {
        guard let first = points.first else { return .null }
        let box = points.dropFirst().reduce(CGRect(origin: first, size: .zero)) { $0.union(CGRect(origin: $1, size: .zero)) }
        return box.insetBy(dx: -width / 2 - 2, dy: -width / 2 - 2)
    }
}

/// How tools/nspec.lua reads a line.
enum RowKind { case blank, prose, heading, bar, formal }

func rowKind(_ line: String) -> RowKind {
    if line.range(of: #"^#+ "#, options: .regularExpression) != nil { return .heading }
    if line.hasPrefix("//") { return .prose }
    if line.allSatisfy(\.isWhitespace) { return .blank }
    var formal = line
    if let note = line.range(of: #"\s+//"#, options: .regularExpression) { formal = String(line[..<note.lowerBound]) }
    let bare = formal.replacingOccurrences(of: #"\([^()]*\)"#, with: "", options: .regularExpression)
    return bare.range(of: #"^\s*---[-\s]*$"#, options: .regularExpression) != nil ? .bar : .formal
}

/// Rows first...last (from 0, inclusive) that the user has edited.
struct Span: Equatable {
    var first: Int
    var last: Int
}

extension Layout {
    /// The rows a mark edits. A pen stroke edits every row whose slot it
    /// passes through; an eraser edits the rows whose text strokes it crosses.
    func rows(editedBy mark: Mark) -> Set<Int> {
        switch mark.tool {
        case .pen:
            return Set(mark.points.compactMap(row(at:)))
        case .eraser:
            let reach = (mark.width + glyphs.pen * Layout.em) / 2
            let path = resample(mark.points, every: max(1, mark.width / 3))
            let (rows, columns) = cells(in: mark.bounds)
            var out = Set<Int>()
            for r in rows where !out.contains(r) {
                cells: for c in columns where c < self.rows[r].count {
                    for stroke in strokes(r, c) where crosses(path, stroke, within: reach) {
                        out.insert(r)
                        break cells
                    }
                }
            }
            return out
        }
    }

    /// The row whose slot holds p, if p is beside the text.
    func row(at p: CGPoint) -> Int? {
        let r = Int((p.y / lineHeight - Layout.margin).rounded(.down))
        return rows.indices.contains(r) ? r : nil
    }
}

/// Edited rows as spans: adjacent rows join.
func spans(of rows: Set<Int>) -> [Span] {
    var out = [Span]()
    for r in rows.sorted() {
        if let last = out.last, last.last + 1 == r { out[out.count - 1].last = r } else { out.append(Span(first: r, last: r)) }
    }
    return out
}

/// The rules among the lines: runs of formal lines with a bar among them.
func rules(in lines: [String]) -> [ClosedRange<Int>] {
    var out = [ClosedRange<Int>]()
    var start: Int?
    var hasBar = false
    for i in 0...lines.count {
        let kind = i < lines.count ? rowKind(lines[i]) : .blank
        if kind == .formal || kind == .bar {
            start = start ?? i
            hasBar = hasBar || kind == .bar
        } else {
            if let s = start, hasBar { out.append(s...(i - 1)) }
            start = nil
            hasBar = false
        }
    }
    return out
}

/// Spans grouped into requests: all spans that touch one rule are read
/// together, as the checker judges a rule as one unit; any other span is a
/// request of its own.
func groupIntoRequests(_ spans: [Span], lines: [String]) -> [[Span]] {
    var parent = Array(spans.indices)
    func root(_ i: Int) -> Int { parent[i] == i ? i : root(parent[i]) }
    for rule in rules(in: lines) {
        let touching = spans.indices.filter { rule.overlaps(spans[$0].first...spans[$0].last) }
        for i in touching.dropFirst() { parent[root(i)] = root(touching[0]) }
    }
    let groups = Dictionary(grouping: spans.indices, by: root).values
    return groups.map { $0.map { spans[$0] } }.sorted { $0[0].first < $1[0].first }
}

/// Rows first...last (from 0) of a text replaced by `lines`; first = last + 1 inserts.
struct Replacement: Equatable {
    let first: Int
    let last: Int
    let lines: [String]

    /// How many lines longer the text is after it.
    var growth: Int { lines.count - (last - first + 1) }
}

/// The text with every replacement made; they must not overlap.
func applying(_ replacements: [Replacement], to lines: [String]) -> [String] {
    var out = lines
    for r in replacements.sorted(by: { $0.first > $1.first }) { out.replaceSubrange(r.first..<(r.last + 1), with: r.lines) }
    return out
}

/// The replacements that undo `replacements` (made to `lines`), in the text
/// they produce: each block sits where the growth of those before it moved it.
func inverse(of replacements: [Replacement], in lines: [String]) -> [Replacement] {
    var shift = 0
    return replacements.sorted(by: { $0.first < $1.first }).map { r in
        defer { shift += r.growth }
        return Replacement(first: r.first + shift, last: r.first + shift + r.lines.count - 1,
                           lines: Array(lines[r.first..<(r.last + 1)]))
    }
}

/// How far row `row` moves when `replacements` are made above it.
func shift(of row: Int, by replacements: [Replacement]) -> Int {
    replacements.filter { $0.last < row }.reduce(0) { $0 + $1.growth }
}

/// Where a replaced block changed, character by character, as cells of the
/// new block (row, column, from 0): the cells written anew, and the places
/// text was removed from (where nothing was written in its stead).
func changes(from old: [String], to new: [String]) -> (written: [Cell], removed: [Cell]) {
    // The lines as one run of characters, newlines between them; each with its cell.
    func run(_ lines: [String]) -> (chars: [Character], cells: [Cell]) {
        var chars = [Character](), cells = [Cell]()
        for (r, line) in lines.enumerated() {
            if r > 0 {
                chars.append("\n")
                cells.append(Cell(row: r - 1, column: lines[r - 1].count))
            }
            for (c, ch) in line.enumerated() {
                chars.append(ch)
                cells.append(Cell(row: r, column: c))
            }
        }
        return (chars, cells)
    }
    let (a, _) = run(old), (b, at) = run(new)
    var gone = Set<Int>(), came = Set<Int>()
    for change in b.difference(from: a) {
        switch change {
        case .remove(let offset, _, _): gone.insert(offset)
        case .insert(let offset, _, _): came.insert(offset)
        }
    }
    // Walk both runs together: what neither removed nor inserted is common, in order.
    var written = [Cell](), removed = [Cell]()
    var i = 0, j = 0
    while i < a.count || j < b.count {
        if i < a.count, gone.contains(i) {
            let spot = j < b.count ? at[j] : at.last.map { Cell(row: $0.row, column: $0.column + 1) } ?? Cell(row: 0, column: 0)
            if removed.last != spot { removed.append(spot) }
            i += 1
        } else if j < b.count, came.contains(j) {
            if b[j] != "\n" { written.append(at[j]) }
            j += 1
        } else {
            i += 1
            j += 1
        }
    }
    return (written, removed.filter { !written.contains($0) })
}

/// A character's place in the text: row and column, from 0.
struct Cell: Hashable {
    let row: Int
    let column: Int
}

// Geometry ---------------------------------------------------------------------

private func resample(_ points: [CGPoint], every step: CGFloat) -> [CGPoint] {
    guard var last = points.first else { return [] }
    var out = [last]
    for p in points.dropFirst() {
        let d = hypot(p.x - last.x, p.y - last.y)
        if d > step {
            let n = Int((d / step).rounded(.up))
            for k in 1..<n { out.append(CGPoint(x: last.x + (p.x - last.x) * CGFloat(k) / CGFloat(n),
                                                y: last.y + (p.y - last.y) * CGFloat(k) / CGFloat(n))) }
        }
        out.append(p)
        last = p
    }
    return out
}

/// Does a densely sampled path come within `reach` of a polyline?
private func crosses(_ path: [CGPoint], _ stroke: [CGPoint], within reach: CGFloat) -> Bool {
    let segments = stroke.count > 1 ? Array(zip(stroke, stroke.dropFirst())) : stroke.map { ($0, $0) }
    return path.contains { p in segments.contains { distance(p, $0.0, $0.1) <= reach } }
}

private func distance(_ p: CGPoint, _ a: CGPoint, _ b: CGPoint) -> CGFloat {
    let (dx, dy) = (b.x - a.x, b.y - a.y)
    let t = dx == 0 && dy == 0 ? 0 : max(0, min(1, ((p.x - a.x) * dx + (p.y - a.y) * dy) / (dx * dx + dy * dy)))
    return hypot(p.x - a.x - t * dx, p.y - a.y - t * dy)
}
