import CoreGraphics

/// One stroke of the Pencil since the last recognition, in page points.
/// Marks apply in order: an eraser clears whatever lies under it, the text's
/// strokes and earlier ink alike; ink drawn after it stays. A lifted
/// character's clearing is the exception: it takes the character out of the
/// text and touches no ink (see `inDrawingOrder`).
struct Mark {
    enum Tool { case pen, eraser }
    let tool: Tool
    let points: [CGPoint]
    let width: CGFloat
    /// The mark's shape to fill, when it has one: a pen stroke whose width
    /// follows the Pencil's pressure, a lifted character's strokes, or the
    /// cell a lifted character leaves (cleared, as an eraser clears). Without
    /// it the stroke is `points` at `width`.
    let ink: CGPath?
    /// For an eraser mark that clears a lifted character's cell: that cell.
    let lifted: Cell?

    init(tool: Tool, points: [CGPoint], width: CGFloat, ink: CGPath? = nil, lifted: Cell? = nil) {
        self.tool = tool
        self.points = points
        self.width = width
        self.ink = ink
        self.lifted = lifted
    }

    /// A pen stroke from the Pencil's samples, smoothed `smoothing` times over.
    init(pen samples: [InkSample], smoothing: CGFloat = defaultSmoothing) {
        let track = smoothed(samples, strength: smoothing)
        self.init(tool: .pen, points: track.map(\.point), width: 2 * (track.map(\.radius).max() ?? 1), ink: inkOutline(track))
    }

    /// The same mark, moved down `rows` rows (when lines above it grew or
    /// shrank); the cell a clearing mark clears moves with it.
    func moved(rows: Int, lineHeight: CGFloat) -> Mark {
        let mark = moved(dx: 0, dy: CGFloat(rows) * lineHeight)
        return Mark(tool: tool, points: mark.points, width: width, ink: mark.ink,
                    lifted: lifted.map { Cell(row: $0.row + rows, column: $0.column) })
    }

    /// The same mark, moved by (dx, dy): ink carried by the move tool.
    func moved(dx: CGFloat, dy: CGFloat) -> Mark {
        var shift = CGAffineTransform(translationX: dx, y: dy)
        return Mark(tool: tool, points: points.map { CGPoint(x: $0.x + dx, y: $0.y + dy) }, width: width,
                    ink: ink.flatMap { $0.copy(using: &shift) }, lifted: lifted)
    }

    /// The mark's points at its width, as a shape to fill.
    var stroke: CGPath {
        let line = CGMutablePath()
        guard let first = points.first else { return line }
        line.move(to: first)
        line.addLines(between: points.count > 1 ? points : [first, first])
        return line.copy(strokingWithWidth: width, lineCap: .round, lineJoin: .round, miterLimit: 1)
    }

    var bounds: CGRect {
        guard let first = points.first else { return .null }
        let box = points.dropFirst().reduce(CGRect(origin: first, size: .zero)) { $0.union(CGRect(origin: $1, size: .zero)) }
        return box.insetBy(dx: -width / 2 - 2, dy: -width / 2 - 2)
    }
}

extension Array where Element == Mark {
    /// The order marks are drawn in: every lifted character's clearing first,
    /// as it removes the character from the text, never ink (ink lifted by
    /// one lasso and moved onto a cell a later lasso lifted must stay whole);
    /// then the ink and the eraser's strokes, in the order they were made.
    var inDrawingOrder: [Mark] { filter { $0.lifted != nil } + filter { $0.lifted == nil } }
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

/// A heading of the text: `#` to `######` and a title, as tools/nspec.lua
/// reads it; its row (from 0) and level (the number of `#`).
struct Heading: Identifiable, Equatable {
    let row: Int
    let level: Int
    let title: String
    var id: Int { row }
}

func headings(of lines: [String]) -> [Heading] {
    lines.enumerated().compactMap { r, line in
        guard rowKind(line) == .heading else { return nil }
        let level = line.prefix { $0 == "#" }.count
        return Heading(row: r, level: level, title: String(line.dropFirst(level)).trimmingCharacters(in: .whitespaces))
    }
}

/// How many edited rows each section holds, by the section's index; a
/// section runs from its heading to the next heading of any level, so a
/// subsection's edits are its own. Rows above the first heading are in none.
func editsBySection(_ edited: Set<Int>, _ sections: [Heading]) -> [Int: Int] {
    var out = [Int: Int]()
    for row in edited {
        // the last heading at or above the row (headings are in row order)
        var lo = 0, hi = sections.count
        while lo < hi {
            let mid = (lo + hi) / 2
            if sections[mid].row <= row { lo = mid + 1 } else { hi = mid }
        }
        if lo > 0 { out[lo - 1, default: 0] += 1 }
    }
    return out
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
            if let cell = mark.lifted { return [cell.row] }
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

// Lasso and lift ---------------------------------------------------------------

extension Layout {
    /// The characters a lasso holds: the cells (not blank ones) whose centre
    /// is inside it.
    func cells(inside lasso: [CGPoint]) -> [Cell] {
        guard lasso.count > 2 else { return [] }
        let box = lasso.dropFirst().reduce(CGRect(origin: lasso[0], size: .zero)) { $0.union(CGRect(origin: $1, size: .zero)) }
        let (rs, cs) = cells(in: box)
        var out = [Cell]()
        for r in rs {
            for c in cs where c < rows[r].count && !rows[r][c].isWhitespace {
                let o = origin(r, c)
                if contains(lasso, CGPoint(x: o.x + cellWidth / 2, y: o.y + lineHeight / 2)) { out.append(Cell(row: r, column: c)) }
            }
        }
        return out
    }

    /// A character lifted out of the text: a mark clearing its cell, and its
    /// strokes as one ink mark, drawn as the glyph is but in ink (no longer
    /// read, so no longer coloured). What the eraser has already taken from
    /// the character (the strokes of `marks` before it) stays taken: only the
    /// rest is lifted, and a character erased whole is not lifted at all.
    func lift(_ cell: Cell, under marks: [Mark] = []) -> [Mark] {
        let o = origin(cell.row, cell.column), box = CGRect(origin: o, size: CGSize(width: cellWidth, height: lineHeight))
        let clear = Mark(tool: .eraser, points: [CGPoint(x: box.minX, y: box.minY), CGPoint(x: box.maxX, y: box.maxY)], width: 0,
                         ink: CGPath(rect: box, transform: nil), lifted: cell)
        let strokes = self.strokes(cell.row, cell.column)
        let path = CGMutablePath()
        for s in strokes {
            guard let first = s.first else { continue }
            path.move(to: first)
            path.addLines(between: s.count > 1 ? s : [first, first])
        }
        let width = glyphs.pen * Layout.em
        var shape = path.copy(strokingWithWidth: width, lineCap: .round, lineJoin: .round, miterLimit: 1)
        for m in marks where m.tool == .eraser && m.lifted == nil && m.bounds.intersects(box) {
            shape = shape.subtracting(m.ink ?? m.stroke)
        }
        guard !shape.boundingBoxOfPath.isEmpty else { return [] }
        return [clear, Mark(tool: .pen, points: strokes.flatMap { $0 }, width: width, ink: shape)]
    }
}

// Revert ------------------------------------------------------------------------

extension Layout {
    /// The rows a traced path passes through (sampled finely enough that a
    /// quick stroke skips none).
    func rows(tracedBy path: [CGPoint]) -> Set<Int> {
        guard var last = path.first else { return [] }
        var out = Set<Int>(row(at: last).map { [$0] } ?? [])
        for p in path.dropFirst() {
            let n = max(1, Int((hypot(p.x - last.x, p.y - last.y) / (lineHeight / 4)).rounded(.up)))
            for k in 1...n {
                let q = CGPoint(x: last.x + (p.x - last.x) * CGFloat(k) / CGFloat(n), y: last.y + (p.y - last.y) * CGFloat(k) / CGFloat(n))
                if let r = row(at: q) { out.insert(r) }
            }
            last = p
        }
        return out
    }

    /// The marks with every edit to `rows` taken back, so those rows show the
    /// text again: a lifted character there goes back into the text (its ink,
    /// moved elsewhere, stays where it went: an edit of that row); every other
    /// mark loses its part over those rows, and a mark left with nothing goes.
    func reverting(_ rows: Set<Int>, in marks: [Mark]) -> [Mark] {
        guard !rows.isEmpty else { return marks }
        let bands = CGMutablePath(), width = size.width
        for r in rows {
            bands.addRect(CGRect(x: -width, y: origin(r, 0).y, width: 3 * width, height: lineHeight))
        }
        func inBand(_ p: CGPoint, reach: CGFloat) -> Bool {
            guard let r = row(at: p) else { return false }
            if rows.contains(r) { return true }
            let top = origin(r, 0).y
            return (rows.contains(r - 1) && p.y - top < reach) || (rows.contains(r + 1) && top + lineHeight - p.y < reach)
        }
        return marks.compactMap { m in
            if let cell = m.lifted { return rows.contains(cell.row) ? nil : m }
            guard m.bounds.intersects(bands.boundingBoxOfPath),
                  m.points.contains(where: { inBand($0, reach: m.width / 2 + glyphs.pen * Layout.em) }) || m.ink != nil
            else { return m }
            let shape = (m.ink ?? m.stroke).subtracting(bands)
            guard !shape.boundingBoxOfPath.isEmpty else { return nil }
            // What is left, and the points that still say where it is (an
            // eraser's reach must not stretch back into the reverted rows).
            let reach = m.tool == .eraser ? m.width / 2 + glyphs.pen * Layout.em : 0
            let kept = m.points.filter { !inBand($0, reach: reach) }
            guard !kept.isEmpty else { return nil }
            return Mark(tool: m.tool, points: kept, width: m.width, ink: shape)
        }
    }
}

/// Is p inside the closed polygon (even-odd)?
func contains(_ polygon: [CGPoint], _ p: CGPoint) -> Bool {
    var inside = false
    var j = polygon.count - 1
    for i in polygon.indices {
        let (a, b) = (polygon[i], polygon[j])
        if (a.y > p.y) != (b.y > p.y), p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x { inside.toggle() }
        j = i
    }
    return inside
}

/// Does a lasso hold a mark: most of its points inside?
func holds(_ lasso: [CGPoint], _ mark: Mark) -> Bool {
    !mark.points.isEmpty && Double(mark.points.filter { contains(lasso, $0) }.count) >= 0.6 * Double(mark.points.count)
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
