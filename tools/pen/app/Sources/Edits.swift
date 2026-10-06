import CoreGraphics

/// One stroke of the Pencil since the last recognition, in page points.
/// Marks apply in order: an eraser clears whatever lies under it, the text's
/// strokes and earlier ink alike; ink drawn after it stays.
struct Mark {
    enum Tool { case pen, eraser }
    let tool: Tool
    let points: [CGPoint]
    let width: CGFloat

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
