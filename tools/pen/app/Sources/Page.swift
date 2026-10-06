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

    /// New text. With `redraw`, only that part of the page is drawn again
    /// (where the text changed); without it, all of it.
    func show(_ layout: Layout, redraw: CGRect? = nil) {
        text = UIColor.label.resolvedColor(with: traitCollection).cgColor
        lock.withLock {
            self.layout = layout
            marks = []
        }
        if let redraw {
            layer.setNeedsDisplay(redraw)
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
        let path = CGMutablePath()
        for r in rows {
            for c in columns where c < layout.rows[r].count {
                for stroke in layout.strokes(r, c) { add(stroke, to: path) }
            }
        }
        ctx.setLineCap(.round)
        ctx.setLineJoin(.round)
        ctx.addPath(path)
        ctx.setStrokeColor(text)
        ctx.setLineWidth(layout.glyphs.pen * Layout.em)
        ctx.strokePath()
        for mark in marks where mark.bounds.intersects(rect) {
            let path = CGMutablePath()
            add(mark.points, to: path)
            ctx.addPath(path)
            ctx.setBlendMode(mark.tool == .eraser ? .clear : .normal)
            ctx.setStrokeColor(ink)
            ctx.setLineWidth(mark.width)
            ctx.strokePath()
        }
        ctx.setBlendMode(.normal)
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
    var tool: () -> Mark.Tool = { .pen }
    var zoom: () -> CGFloat = { 1 }

    private var points: [CGPoint] = []
    private let live = CAShapeLayer()
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

    override func touchesBegan(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil else { return }
        points = [touch.location(in: self)]
        let eraser = tool() == .eraser
        live.strokeColor = eraser ? UIColor.systemGray.withAlphaComponent(0.35).cgColor : UIColor.systemBlue.cgColor
        live.lineWidth = (eraser ? InkView.eraserWidth : InkView.penWidth) / zoom()
        redraw()
    }

    override func touchesMoved(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil, !points.isEmpty else { return }
        points += (event?.coalescedTouches(for: touch) ?? [touch]).map { $0.location(in: self) }
        redraw()
    }

    override func touchesEnded(_ touches: Set<UITouch>, with event: UIEvent?) {
        guard let touch = touches.first, touch.type == .pencil, !points.isEmpty else { return }
        points += (event?.coalescedTouches(for: touch) ?? [touch]).map { $0.location(in: self) }
        let tool = tool()
        onMark?(Mark(tool: tool, points: points, width: (tool == .eraser ? InkView.eraserWidth : InkView.penWidth) / zoom()))
        points = []
        redraw()
    }

    override func touchesCancelled(_ touches: Set<UITouch>, with event: UIEvent?) {
        points = []
        redraw()
    }

    private func redraw() {
        CATransaction.begin()
        CATransaction.setDisableActions(true)
        let path = CGMutablePath()
        if let first = points.first {
            path.move(to: first)
            path.addLines(between: points.count > 1 ? points : [first, first])
        }
        live.path = path
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

    func show(_ layout: Layout, redraw: CGRect? = nil) {
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
