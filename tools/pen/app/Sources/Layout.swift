import CoreGraphics

/// The text as a grid of cells, one per character (a base with its marks),
/// drawn as strokes. Where a character sits is a function of the text alone:
/// row r, column c is at `origin(r, c)`.
struct Layout {
    static let em: CGFloat = 20 // points per em at zoom 1
    static let margin: CGFloat = 2 // cells of margin on every side

    let rows: [[Character]]
    let glyphs: Glyphs
    /// Each cell's token kind, from the checker; nil (or missing) draws plain.
    var kinds: [[TokenKind?]] = []

    /// A layout of lines and their tokens.
    init(rows: [[Character]], glyphs: Glyphs, kinds: [[TokenKind?]] = []) {
        self.rows = rows
        self.glyphs = glyphs
        self.kinds = kinds
    }

    init(lines: [String], tokens: [[Token]], glyphs: Glyphs) {
        self.init(rows: lines.map(Array.init), glyphs: glyphs,
                  kinds: zip(lines, tokens).map { cellKinds($0, $1) })
    }

    func kind(_ r: Int, _ c: Int) -> TokenKind? {
        kinds.indices.contains(r) && kinds[r].indices.contains(c) ? kinds[r][c] : nil
    }

    var cellWidth: CGFloat { glyphs.cell * Layout.em }
    var lineHeight: CGFloat { (glyphs.ascent + glyphs.descent) * Layout.em }
    var size: CGSize {
        let columns = rows.map(\.count).max() ?? 0
        return CGSize(width: (CGFloat(columns) + 2 * Layout.margin) * cellWidth,
                      height: (CGFloat(rows.count) + 2 * Layout.margin) * lineHeight)
    }

    /// The top-left corner of the cell at row r, column c (both from 0).
    func origin(_ r: Int, _ c: Int) -> CGPoint {
        CGPoint(x: (CGFloat(c) + Layout.margin) * cellWidth, y: (CGFloat(r) + Layout.margin) * lineHeight)
    }

    /// The rows and columns whose cells meet rect.
    func cells(in rect: CGRect) -> (rows: Range<Int>, columns: Range<Int>) {
        func span(_ lo: CGFloat, _ hi: CGFloat, _ step: CGFloat, _ count: Int) -> Range<Int> {
            let a = max(0, Int((lo / step - Layout.margin).rounded(.down)))
            let b = min(count, Int((hi / step - Layout.margin).rounded(.up)))
            return a < b ? a..<b : 0..<0
        }
        let columns = rows.map(\.count).max() ?? 0
        return (span(rect.minY, rect.maxY, lineHeight, rows.count), span(rect.minX, rect.maxX, cellWidth, columns))
    }

    /// The strokes of the cell at row r, column c, in page points.
    func strokes(_ r: Int, _ c: Int) -> [[CGPoint]] {
        let o = origin(r, c), baseline = o.y + glyphs.ascent * Layout.em
        return glyphs.strokes(of: rows[r][c]).map { $0.map { CGPoint(x: o.x + $0.x * Layout.em, y: baseline - $0.y * Layout.em) } }
    }
}
