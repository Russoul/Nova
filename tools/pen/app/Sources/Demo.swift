#if DEBUG
import UIKit

/// A scripted edit, for checking the app where no Pencil can draw (the
/// simulator driven from the command line). Launch arguments:
///   -demo-ink        once the text is shown, erase the a₂ of the first
///                    `Γ ⊦ a₀ ≐ a₂ : A` and write b₁ above it
///   -demo-recognise  then press Recognise
///   -demo-undo       then press Undo
///   -demo-move       instead of writing: lasso that a₂ and move it two rows down
///   -demo-revert     after the ink: revert the bar's line (the ink reaching it is trimmed)
///   -demo-shift      instead: erase the last 6 dashes of el-trans's bar, lasso
///                    its name and note, and move them 6 cells left
@MainActor
enum Demo {
    static var ink: Bool { ProcessInfo.processInfo.arguments.contains("-demo-ink") }
    static var recognise: Bool { ProcessInfo.processInfo.arguments.contains("-demo-recognise") }
    static var undo: Bool { ProcessInfo.processInfo.arguments.contains("-demo-undo") }
    static var move: Bool { ProcessInfo.processInfo.arguments.contains("-demo-move") }
    static var shift: Bool { ProcessInfo.processInfo.arguments.contains("-demo-shift") }
    static var revert: Bool { ProcessInfo.processInfo.arguments.contains("-demo-revert") }
    private static var done = false

    static func run(_ editor: Editor, _ relay: Relay) {
        guard ink || move || shift, !done, let layout = editor.layoutShown,
              let row = editor.lines.firstIndex(of: "Γ ⊦ a₀ ≐ a₂ : A"),
              let at = Array(editor.lines[row]).firstIndex(of: "≐") else { return }
        done = true
        let col = at + 2, a = layout.origin(row, col), cw = layout.cellWidth, lh = layout.lineHeight
        if shift {
            let bar = row - 1, dashes = Array(editor.lines[bar]).prefix { $0 == "-" }.count
            let o = layout.origin(bar, 0), y = o.y + lh / 2
            editor.tool = .eraser
            editor.add(Mark(tool: .eraser, points: [CGPoint(x: o.x + CGFloat(dashes - 6) * cw, y: y), CGPoint(x: o.x + CGFloat(dashes) * cw, y: y)], width: 8))
            editor.tool = .lasso
            let end = o.x + CGFloat(editor.lines[bar].count + 1) * cw
            editor.lasso([CGPoint(x: o.x + CGFloat(dashes) * cw + 2, y: o.y + 3), CGPoint(x: end, y: o.y + 3),
                          CGPoint(x: end, y: o.y + lh - 3), CGPoint(x: o.x + CGFloat(dashes) * cw + 2, y: o.y + lh - 3)])
            editor.moveSelection(by: CGVector(dx: -6 * cw, dy: 0))
            editor.scroll?.zoom(to: CGRect(x: o.x + CGFloat(dashes - 20) * cw, y: o.y - 3 * lh, width: 40 * cw, height: 7 * lh), animated: false)
            return
        }
        if move {
            editor.tool = .lasso
            editor.lasso([CGPoint(x: a.x - 3, y: a.y + 3), CGPoint(x: a.x + 2 * cw + 3, y: a.y + 3),
                          CGPoint(x: a.x + 2 * cw + 3, y: a.y + lh - 3), CGPoint(x: a.x - 3, y: a.y + lh - 3)])
            editor.moveSelection(by: CGVector(dx: 0, dy: 2 * lh))
            editor.scroll?.zoom(to: CGRect(x: a.x - 12 * cw, y: a.y - 4 * lh, width: 30 * cw, height: 8 * lh), animated: false)
            if recognise { Task { await editor.recognise(with: relay) } }
            return
        }
        let zigzag = (0...8).map { k in CGPoint(x: a.x + cw * 2 * CGFloat(k) / 8, y: a.y + lh * (k % 2 == 0 ? 0.3 : 0.8)) }
        editor.add(Mark(tool: .eraser, points: zigzag, width: 6))
        var x = a.x
        for ch in ["b", "₁"] {
            for stroke in layout.glyphs.strokes(of: Character(ch)) {
                let samples = stroke.enumerated().map { k, p in
                    InkSample(point: CGPoint(x: x + p.x * Layout.em * 1.3 + sin(CGFloat(k)) * 0.6,
                                             y: a.y - lh * 0.15 - p.y * Layout.em * 1.3 + cos(CGFloat(k) * 1.7) * 0.6),
                              radius: inkRadius(base: 0.6, pressure: 0.3 + 0.5 * sin(.pi * CGFloat(k) / CGFloat(max(stroke.count - 1, 1)))))
                }
                editor.add(Mark(pen: samples))
            }
            x += cw * 1.3
        }
        editor.scroll?.zoom(to: CGRect(x: a.x - 12 * cw, y: a.y - 4 * lh, width: 30 * cw, height: 8 * lh), animated: false)
        if revert {
            let bar = layout.origin(row - 1, 0)
            editor.revert([CGPoint(x: bar.x, y: bar.y + lh / 2), CGPoint(x: bar.x + 40 * cw, y: bar.y + lh / 2)])
        }
        guard recognise else { return }
        Task {
            await editor.recognise(with: relay)
            if undo { await editor.undo(with: relay) }
        }
    }
}
#endif
