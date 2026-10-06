#if DEBUG
import UIKit

/// A scripted edit, for checking the app where no Pencil can draw (the
/// simulator driven from the command line). Launch arguments:
///   -demo-ink        once the text is shown, erase the a₂ of the first
///                    `Γ ⊦ a₀ ≐ a₂ : A` and write b₁ above it
///   -demo-recognise  then press Recognise
///   -demo-undo       then press Undo
@MainActor
enum Demo {
    static var ink: Bool { ProcessInfo.processInfo.arguments.contains("-demo-ink") }
    static var recognise: Bool { ProcessInfo.processInfo.arguments.contains("-demo-recognise") }
    static var undo: Bool { ProcessInfo.processInfo.arguments.contains("-demo-undo") }
    private static var done = false

    static func run(_ editor: Editor, _ relay: Relay) {
        guard ink, !done, let layout = editor.layoutShown,
              let row = editor.lines.firstIndex(of: "Γ ⊦ a₀ ≐ a₂ : A"),
              let at = Array(editor.lines[row]).firstIndex(of: "≐") else { return }
        done = true
        let col = at + 2, a = layout.origin(row, col), cw = layout.cellWidth, lh = layout.lineHeight
        let zigzag = (0...8).map { k in CGPoint(x: a.x + cw * 2 * CGFloat(k) / 8, y: a.y + lh * (k % 2 == 0 ? 0.3 : 0.8)) }
        editor.add(Mark(tool: .eraser, points: zigzag, width: 6))
        var x = a.x
        for ch in ["b", "₁"] {
            for stroke in layout.glyphs.strokes(of: Character(ch)) {
                let points = stroke.enumerated().map { k, p in
                    CGPoint(x: x + p.x * Layout.em * 1.3 + sin(CGFloat(k)) * 0.6,
                            y: a.y - lh * 0.15 - p.y * Layout.em * 1.3 + cos(CGFloat(k) * 1.7) * 0.6)
                }
                editor.add(Mark(tool: .pen, points: points.count > 1 ? points : points + points, width: 1.2))
            }
            x += cw * 1.3
        }
        editor.scroll?.zoom(to: CGRect(x: a.x - 12 * cw, y: a.y - 4 * lh, width: 30 * cw, height: 8 * lh), animated: false)
        guard recognise else { return }
        Task {
            await editor.recognise(with: relay)
            if undo { await editor.undo(with: relay) }
        }
    }
}
#endif
