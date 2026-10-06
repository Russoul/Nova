import CoreGraphics
import Foundation

/// The stroke glyphs tools/pen/glyphs.py extracts from the font: for each
/// character, polylines in em units from the cell's origin on the baseline,
/// y up. Text is drawn from these, never from a font.
final class Glyphs {
    /// Cell width, ascent, descent and pen width, in em.
    let cell, ascent, descent, pen: CGFloat
    private let strokes: [Unicode.Scalar: [[CGPoint]]]

    static let bundled: Glyphs = {
        guard let url = Bundle.main.url(forResource: "glyphs", withExtension: "json"),
              let glyphs = try? Glyphs(url: url) else { fatalError("glyphs.json is missing or malformed") }
        return glyphs
    }()

    init(url: URL) throws {
        guard let json = try JSONSerialization.jsonObject(with: Data(contentsOf: url)) as? [String: Any],
              let cell = json["cell"] as? [String: Double], let pen = json["pen"] as? Double,
              let glyphs = json["glyphs"] as? [String: [[[Double]]]],
              let width = cell["width"], let ascent = cell["ascent"], let descent = cell["descent"]
        else { throw CocoaError(.fileReadCorruptFile) }
        self.cell = width
        self.ascent = ascent
        self.descent = descent
        self.pen = pen
        var map = [Unicode.Scalar: [[CGPoint]]]()
        for (key, value) in glyphs {
            guard key.unicodeScalars.count == 1, let scalar = key.unicodeScalars.first else { continue }
            map[scalar] = value.map { $0.map { CGPoint(x: $0[0], y: $0[1]) } }
        }
        strokes = map
    }

    /// The strokes of one cell: a character's base and its combining marks,
    /// drawn together. A scalar with no glyph is drawn as an empty box.
    func strokes(of ch: Character) -> [[CGPoint]] {
        ch.unicodeScalars.flatMap { strokes[$0] ?? box }
    }

    private var box: [[CGPoint]] {
        let (l, r, b, t) = (cell * 0.15, cell * 0.85, 0.0, ascent * 0.75)
        return [[CGPoint(x: l, y: b), CGPoint(x: r, y: b), CGPoint(x: r, y: t), CGPoint(x: l, y: t), CGPoint(x: l, y: b)]]
    }
}
