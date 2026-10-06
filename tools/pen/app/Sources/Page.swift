import UIKit

/// The page: the text's strokes, drawn tile by tile (only what is on screen,
/// at the zoom it is seen at).
final class PageView: UIView {
    override class var layerClass: AnyClass { CATiledLayer.self }

    private let lock = NSLock()
    private var layout: Layout?
    private var ink = UIColor.label.cgColor

    override init(frame: CGRect) {
        super.init(frame: frame)
        let tiled = layer as! CATiledLayer
        tiled.tileSize = CGSize(width: 512, height: 512)
        tiled.levelsOfDetail = 4 // zoomed out down to 1/8
        tiled.levelsOfDetailBias = 4 // zoomed in up to 16x, still sharp
        backgroundColor = .clear
    }

    required init?(coder: NSCoder) { fatalError("not from a storyboard") }

    func show(_ layout: Layout) {
        ink = UIColor.label.resolvedColor(with: traitCollection).cgColor
        lock.withLock { self.layout = layout }
        layer.contents = nil
        layer.setNeedsDisplay()
    }

    override func draw(_ rect: CGRect) {
        guard let ctx = UIGraphicsGetCurrentContext(), let layout = lock.withLock({ self.layout }) else { return }
        let (rows, columns) = layout.cells(in: rect)
        let path = CGMutablePath()
        for r in rows {
            for c in columns where c < layout.rows[r].count {
                for stroke in layout.strokes(r, c) {
                    guard let first = stroke.first else { continue }
                    path.move(to: first)
                    path.addLines(between: stroke.count > 1 ? stroke : [first, first]) // a dot: a round cap
                }
            }
        }
        ctx.addPath(path)
        ctx.setStrokeColor(ink)
        ctx.setLineWidth(layout.glyphs.pen * Layout.em)
        ctx.setLineCap(.round)
        ctx.setLineJoin(.round)
        ctx.strokePath()
    }
}

/// The page in a scroll view: fingers pan and pinch; the Pencil is left for ink.
final class PageScroll: UIScrollView, UIScrollViewDelegate {
    let page = PageView(frame: .zero)

    override init(frame: CGRect) {
        super.init(frame: frame)
        addSubview(page)
        delegate = self
        minimumZoomScale = 0.2
        maximumZoomScale = 16
        backgroundColor = .systemBackground
        panGestureRecognizer.allowedTouchTypes = [NSNumber(value: UITouch.TouchType.direct.rawValue)]
        pinchGestureRecognizer?.allowedTouchTypes = [NSNumber(value: UITouch.TouchType.direct.rawValue)]
    }

    required init?(coder: NSCoder) { fatalError("not from a storyboard") }

    func show(_ layout: Layout) {
        let size = layout.size
        page.bounds = CGRect(origin: .zero, size: size)
        page.center = CGPoint(x: size.width * zoomScale / 2, y: size.height * zoomScale / 2)
        contentSize = CGSize(width: size.width * zoomScale, height: size.height * zoomScale)
        page.show(layout)
    }

    func viewForZooming(in scrollView: UIScrollView) -> UIView? { page }
}
