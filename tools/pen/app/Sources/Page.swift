import UIKit

/// The page: the text's strokes, then the marks over them in order (ink in
/// blue; an eraser clears what lies under it), drawn tile by tile, only what
/// is on screen and at the zoom it is seen at.
final class PageView: UIView {
    override class var layerClass: AnyClass { CATiledLayer.self }

    private let lock = NSLock()
    private var layout: Layout?
    private var marks: [Mark] = []
    private var text = UIColor.label.cgColor
    private var palette: [TokenKind: CGColor] = [:]
    private var numbers = UIColor.tertiaryLabel.cgColor
    private let ink = UIColor.systemBlue.cgColor

    override init(frame: CGRect) {
        super.init(frame: frame)
        let tiled = layer as! CATiledLayer
        tiled.tileSize = CGSize(width: 512, height: 512)
        tiled.levelsOfDetail = 4 // zoomed out down to 1/8
        tiled.levelsOfDetailBias = 4 // zoomed in up to 16x, still sharp
        backgroundColor = .clear
    }

    required init?(coder: NSCoder) { fatalError("not from a storyboard") }

    /// New text. With `redraw`, only those parts of the page are drawn again
    /// (where the text or its colours changed); without it, all of it.
    func show(_ layout: Layout, redraw: [CGRect]? = nil) {
        text = UIColor.label.resolvedColor(with: traitCollection).cgColor
        palette = TokenKind.palette(for: traitCollection)
        numbers = UIColor.tertiaryLabel.resolvedColor(with: traitCollection).cgColor
        lock.withLock {
            self.layout = layout
            marks = []
        }
        if let redraw {
            redraw.forEach { layer.setNeedsDisplay($0) }
        } else {
            layer.contents = nil
            layer.setNeedsDisplay()
        }
    }

    /// The marks now; `changed` is where they differ from before.
    func show(_ marks: [Mark], changed: CGRect) {
        lock.withLock { self.marks = marks }
        if !changed.isNull { layer.setNeedsDisplay(changed) }
    }

    override func draw(_ rect: CGRect) {
        guard let ctx = UIGraphicsGetCurrentContext() else { return }
        let (layout, marks) = lock.withLock { (self.layout, self.marks) }
        guard let layout else { return }
        let (rows, columns) = layout.cells(in: rect)
        var paths: [TokenKind?: CGMutablePath] = [:] // one path per kind, plain text under nil
        for r in rows {
            for c in columns where c < layout.rows[r].count {
                let kind = layout.kind(r, c), path = paths[kind] ?? CGMutablePath()
                for stroke in layout.strokes(r, c) { add(stroke, to: path) }
                paths[kind] = path
            }
        }
        ctx.setLineCap(.round)
        ctx.setLineJoin(.round)
        ctx.setLineWidth(layout.glyphs.pen * Layout.em)
        for (kind, path) in paths {
            ctx.addPath(path)
            ctx.setStrokeColor(kind.flatMap { palette[$0] } ?? text)
            ctx.strokePath()
        }
        for mark in marks.inDrawingOrder where mark.bounds.intersects(rect) {
            if let ink = mark.ink {
                ctx.setBlendMode(mark.tool == .eraser ? .clear : .normal) // a lifted character's cell is cleared
                ctx.addPath(ink)
                ctx.setFillColor(self.ink)
                ctx.fillPath()
                continue
            }
            let path = CGMutablePath()
            add(mark.points, to: path)
            ctx.addPath(path)
            ctx.setBlendMode(mark.tool == .eraser ? .clear : .normal)
            ctx.setStrokeColor(ink)
            ctx.setLineWidth(mark.width)
            ctx.strokePath()
        }
        ctx.setBlendMode(.normal)
        // Line numbers last: over any ink, so nothing erases them.
        if layout.numbered {
            let path = CGMutablePath()
            for r in rows { for stroke in layout.numberStrokes(r) { add(stroke, to: path) } }
            ctx.addPath(path)
            ctx.setStrokeColor(numbers)
            ctx.setLineWidth(layout.glyphs.pen * Layout.em)
            ctx.strokePath()
        }
    }

    private func add(_ stroke: [CGPoint], to path: CGMutablePath) {
        guard let first = stroke.first else { return }
        path.move(to: first)
        path.addLines(between: stroke.count > 1 ? stroke : [first, first]) // a dot: a round cap
    }
}

/// Over the page: takes the Pencil's strokes (fingers pass through to the
/// scroll view), shows the stroke being drawn, and tints the edited spans,
/// one colour per request.
final class InkView: UIView {
    var onMark: ((Mark) -> Void)?
    /// A lasso drawn, closed; the start, travel and end of a move (false
    /// from onMoveBegan: nothing is selected, so nothing moves).
    var onLasso: (([CGPoint]) -> Void)?
    /// A path traced with the revert tool.
    var onRevert: (([CGPoint]) -> Void)?
    var onMoveBegan: (() -> Bool)?
    var onMove: ((CGVector) -> Void)?
    var onMoveEnded: ((CGVector) -> Void)?
    var tool: () -> PenTool = { .pen }
    var zoom: () -> CGFloat = { 1 }
    var smoothing: () -> CGFloat = { 1 }

    private var samples: [InkSample] = []
    private var predicted: [InkSample] = []
    private var drawing: PenTool = .pen
    private var moving: CGPoint?
    private let live = CAShapeLayer()
    private let selection = CAShapeLayer()
    private let dragged = CAShapeLayer()
    private var bands: [CAShapeLayer] = []
    private var flashing: CALayer?
    private static let tints: [UIColor] = [.systemOrange, .systemGreen, .systemPink, .systemTeal, .systemPurple, .systemYellow]

    /// Pen and eraser widths stay the same on screen whatever the zoom.
    static let penWidth: CGFloat = 2.5, eraserWidth: CGFloat = 18

    override init(frame: CGRect) {
        super.init(frame: frame)
        backgroundColor = .clear
        isMultipleTouchEnabled = false
        live.fillColor = nil
        live.lineCap = .round
        live.lineJoin = .round
        layer.addSublayer(live)
        selection.fillColor = nil
        selection.strokeColor = UIColor.systemBlue.cgColor
        layer.addSublayer(selection)
        dragged.fillColor = UIColor.systemBlue.cgColor
        layer.addSublayer(dragged)
    }

    required init?(coder: NSCoder) { fatalError("not from a storyboard") }

    /// Tint the spans: rects across the page, grouped by request.
    func show(_ requests: [[Span]], in layout: Layout) {
        bands.forEach { $0.removeFromSuperlayer() }
        bands = requests.enumerated().map { k, spans in
            let band = CAShapeLayer()
            let path = CGMutablePath()
            for s in spans {
                let top = layout.origin(s.first, 0).y, bottom = layout.origin(s.last, 0).y + layout.lineHeight
                path.addRect(CGRect(x: 0, y: top, width: bounds.width, height: bottom - top))
            }
            band.path = path
            band.fillColor = InkView.tints[k % InkView.tints.count].withAlphaComponent(0.14).cgColor
            layer.insertSublayer(band, below: live)
            return band
        }
    }

    /// Show briefly what a text edit changed: cells written anew tinted, with
    /// their characters drawn over everything (text restored by an undo can
    /// lie under the eraser that comes back with it), and a bar where text
    /// was removed; then fade. A new flash replaces one still showing.
    func flash(written: [Cell], removed: [Cell], in layout: Layout) {
        flashing?.removeFromSuperlayer()
        guard !written.isEmpty || !removed.isEmpty else { return }
        let cw = layout.cellWidth, lh = layout.lineHeight
        let tint = CAShapeLayer(), bars = CAShapeLayer(), glyphs = CAShapeLayer()
        let tintPath = CGMutablePath(), barPath = CGMutablePath(), glyphPath = CGMutablePath()
        for cell in written {
            tintPath.addRect(CGRect(origin: layout.origin(cell.row, cell.column), size: CGSize(width: cw, height: lh)))
            for stroke in layout.strokes(cell.row, cell.column) {
                guard let first = stroke.first else { continue }
                glyphPath.move(to: first)
                glyphPath.addLines(between: stroke.count > 1 ? stroke : [first, first])
            }
        }
        glyphs.path = glyphPath
        glyphs.fillColor = nil
        glyphs.strokeColor = UIColor.systemGreen.cgColor
        glyphs.lineWidth = layout.glyphs.pen * Layout.em
        glyphs.lineCap = .round
        glyphs.lineJoin = .round
        for cell in removed {
            let o = layout.origin(cell.row, cell.column)
            barPath.addRect(CGRect(x: o.x - lh * 0.04, y: o.y + lh * 0.1, width: lh * 0.08, height: lh * 0.8))
        }
        tint.path = tintPath
        tint.fillColor = UIColor.systemGreen.withAlphaComponent(0.3).cgColor
        bars.path = barPath
        bars.fillColor = UIColor.systemRed.withAlphaComponent(0.8).cgColor
        let group = CALayer()
        group.addSublayer(tint)
        group.addSublayer(glyphs)
        group.addSublayer(bars)
        layer.insertSublayer(group, below: live)
        flashing = group
        let fade = CABasicAnimation(keyPath: "opacity")
        fade.fromValue = 1
        fade.toValue = 0
        fade.beginTime = CACurrentMediaTime() + 1.0
        fade.duration = 1.0
        fade.fillMode = .forwards
        fade.isRemovedOnCompletion = false
        group.add(fade, forKey: "fade")
        DispatchQueue.main.asyncAfter(deadline: .now() + 2.1) { [weak self] in
            group.removeFromSuperlayer()
            if self?.flashing === group { self?.flashing = nil }
        }
    }

    /// A dashed box around what is selected, or none.
    func showSelection(_ box: CGRect?) {
        CATransaction.begin()
        CATransaction.setDisableActions(true)
        selection.path = box.map { CGPath(rect: $0.insetBy(dx: -4, dy: -4), transform: nil) }
        selection.lineWidth = 1.5 / zoom()
        selection.lineDashPattern = [NSNumber(value: Double(6 / zoom())), NSNumber(value: Double(4 / zoom()))]
        CATransaction.commit()
    }

    /// What is being moved, drawn over the page `offset` from where it was.
    func showDragged(_ path: CGPath?, offset: CGVector) {
        CATransaction.begin()
        CATransaction.setDisableActions(true)
        dragged.path = path
        dragged.setAffineTransform(CGAffineTransform(translationX: offset.dx, y: offset.dy))
        CATransaction.commit()
    }

    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil else { return }
        drawing = tool()
        if drawing == .move {
            moving = onMoveBegan?() == true ? touch.location(in: self) : nil
            return
        }
        samples = [sample(touch)]
        predicted = []
        if drawing == .lasso {
            live.fillColor = UIColor.systemBlue.withAlphaComponent(0.06).cgColor
            live.strokeColor = UIColor.systemBlue.cgColor
            live.lineWidth = 1.5 / zoom()
            live.lineDashPattern = [NSNumber(value: Double(6 / zoom())), NSNumber(value: Double(4 / zoom()))]
        } else if drawing == .revert {
            live.lineDashPattern = nil
            live.fillColor = nil
            live.strokeColor = UIColor.systemOrange.withAlphaComponent(0.4).cgColor
            live.lineWidth = 12 / zoom()
        } else if drawing == .eraser {
            live.lineDashPattern = nil
            live.fillColor = nil
            live.strokeColor = UIColor.systemGray.withAlphaComponent(0.35).cgColor
            live.lineWidth = InkView.eraserWidth / zoom()
        } else {
            live.lineDashPattern = nil
            live.fillColor = UIColor.systemBlue.cgColor
            live.strokeColor = nil
            live.lineWidth = 0
        }
        redraw()
    }

    override func touchesMoved(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil else { return }
        if drawing == .move {
            if let start = moving { onMove?(offset(from: start, to: touch)) }
            return
        }
        guard !samples.isEmpty else { return }
        samples += (event?.coalescedTouches(for: touch) ?? [touch]).map(sample)
        // Where the Pencil is about to be: shown now, replaced by what it does.
        predicted = (event?.predictedTouches(for: touch) ?? []).map(sample)
        redraw()
    }

    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil else { return }
        if drawing == .move {
            if let start = moving { onMoveEnded?(offset(from: start, to: touch)) }
            moving = nil
            return
        }
        guard !samples.isEmpty else { return }
        samples += (event?.coalescedTouches(for: touch) ?? [touch]).map(sample)
        switch drawing {
        case .eraser: onMark?(Mark(tool: .eraser, points: samples.map(\.point), width: InkView.eraserWidth / zoom()))
        case .lasso: onLasso?(samples.map(\.point))
        case .revert: onRevert?(samples.map(\.point))
        default: onMark?(Mark(pen: samples, smoothing: smoothing()))
        }
        samples = []
        predicted = []
        redraw()
    }

    override func touchesCancelled(_ touches: Set<UITouch>, with event: UIEvent?) {
        if drawing == .move, moving != nil {
            onMoveEnded?(.zero)
            moving = nil
        }
        samples = []
        predicted = []
        redraw()
    }

    private func offset(from start: CGPoint, to touch: UITouch) -> CGVector {
        let p = touch.location(in: self)
        return CGVector(dx: p.x - start.x, dy: p.y - start.y)
    }

    /// Where a touch is, and the pen's radius there: wider the harder the
    /// Pencil presses, and the same on screen whatever the zoom.
    private func sample(_ touch: UITouch) -> InkSample {
        let pressure = touch.maximumPossibleForce > 0 ? touch.force / touch.maximumPossibleForce : 0.5
        return InkSample(point: touch.location(in: self), radius: inkRadius(base: InkView.penWidth / 2 / zoom(), pressure: pressure))
    }

    private func redraw() {
        CATransaction.begin()
        CATransaction.setDisableActions(true)
        let track = samples + predicted
        if drawing == .lasso {
            let path = CGMutablePath()
            if let first = track.first {
                path.move(to: first.point)
                path.addLines(between: track.map(\.point))
                path.closeSubpath()
            }
            live.path = path
        } else if drawing == .eraser || drawing == .revert {
            let path = CGMutablePath()
            if let first = track.first {
                path.move(to: first.point)
                path.addLines(between: track.count > 1 ? track.map(\.point) : [first.point, first.point])
            }
            live.path = path
        } else {
            live.path = inkOutline(smoothed(track, strength: smoothing()))
        }
        CATransaction.commit()
    }
}

/// The page in a scroll view: fingers pan and pinch; the Pencil writes and erases.
final class PageScroll: UIScrollView, UIScrollViewDelegate {
    let page = PageView(frame: .zero)
    let ink = InkView(frame: .zero)

    override init(frame: CGRect) {
        super.init(frame: frame)
        addSubview(page)
        page.addSubview(ink)
        ink.autoresizingMask = [.flexibleWidth, .flexibleHeight]
        ink.zoom = { [unowned self] in zoomScale }
        delegate = self
        minimumZoomScale = 0.2
        maximumZoomScale = 16
        delaysContentTouches = false // a Pencil stroke starts at once
        backgroundColor = .systemBackground
        panGestureRecognizer.allowedTouchTypes = [NSNumber(value: UITouch.TouchType.direct.rawValue)]
        pinchGestureRecognizer?.allowedTouchTypes = [NSNumber(value: UITouch.TouchType.direct.rawValue)]
    }

    required init?(coder: NSCoder) { fatalError("not from a storyboard") }

    func show(_ layout: Layout, redraw: [CGRect]? = nil) {
        let size = layout.size
        page.bounds = CGRect(origin: .zero, size: size)
        page.center = CGPoint(x: size.width * zoomScale / 2, y: size.height * zoomScale / 2)
        contentSize = CGSize(width: size.width * zoomScale, height: size.height * zoomScale)
        ink.frame = page.bounds
        page.show(layout, redraw: redraw)
        ink.show([], in: layout)
    }

    func viewForZooming(in scrollView: UIScrollView) -> UIView? { page }
}

extension TokenKind {
    /// The colours of the kinds: tools/nspec.lua's `M.colours` on a dark page
    /// (as in Neovim), and darker twins of the same hues on a light one.
    /// A heading takes the page's own text colour, as in Neovim.
    static func palette(for traits: UITraitCollection) -> [TokenKind: CGColor] {
        let dark = traits.userInterfaceStyle == .dark
        var out = [TokenKind: CGColor]()
        for kind in [TokenKind.prose, .bar, .rule, .keyword, .nova, .level, .index, .tos, .proof] {
            let (onDark, onLight): (UInt32, UInt32) = switch kind {
            case .prose: (0xa6adc8, 0x6c6f85)
            case .bar: (0x6c7086, 0x9ca0b0)
            case .rule: (0xa995d6, 0x7254b8)
            case .keyword: (0xf9e2af, 0xb7791f)
            case .nova: (0x5c6370, 0x7c7f93)
            case .level, .index: (0xfab387, 0xd2560a)
            case .tos: (0x53cad4, 0x14838c)
            case .proof: (0xcba6f7, 0x8839ef)
            case .heading: (0, 0)
            }
            let rgb = dark ? onDark : onLight
            out[kind] = CGColor(srgbRed: CGFloat(rgb >> 16 & 0xff) / 255, green: CGFloat(rgb >> 8 & 0xff) / 255,
                                blue: CGFloat(rgb & 0xff) / 255, alpha: 1)
        }
        return out
    }
}
