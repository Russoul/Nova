import CoreGraphics
import Foundation
import ImageIO
import UniformTypeIdentifiers

extension Layout {
    /// The picture of a span that Claude reads: the original text in grey,
    /// the eraser's paths in red over what they erased, new ink in blue, on
    /// white. It shows a line of context above and below, and only the
    /// columns around the marks: a whole long line, shrunk to fit an image,
    /// would leave the handwriting too small to read.
    func composite(of span: Span, marks: [Mark], scale: CGFloat = 3) -> Data? {
        let above = max(0, span.first - 1), below = min(rows.count - 1, span.last + 1)
        let band = CGRect(x: 0, y: origin(above, 0).y, width: size.width,
                          height: origin(below, 0).y + lineHeight - origin(above, 0).y)
        let touching = marks.filter { $0.bounds.intersects(band) }
        let inked = touching.reduce(CGRect.null) { $0.union($1.bounds) }
        let room = 12 * cellWidth
        let left = max(0, (inked.isNull ? 0 : inked.minX) - room)
        let textEnd = (above...below).map { origin($0, rows[$0].count).x }.max() ?? 0
        let right = max(inked.isNull ? 0 : inked.maxX, min(textEnd, (inked.isNull ? 0 : inked.maxX) + room)) + cellWidth
        let crop = CGRect(x: left, y: band.minY, width: right - left, height: band.height)

        let width = Int(crop.width * scale), height = Int(crop.height * scale)
        guard width > 0, height > 0,
              let ctx = CGContext(data: nil, width: width, height: height, bitsPerComponent: 8, bytesPerRow: 0,
                                  space: CGColorSpaceCreateDeviceRGB(),
                                  bitmapInfo: CGImageAlphaInfo.premultipliedLast.rawValue)
        else { return nil }
        ctx.setFillColor(CGColor(red: 1, green: 1, blue: 1, alpha: 1))
        ctx.fill(CGRect(x: 0, y: 0, width: width, height: height))
        ctx.translateBy(x: 0, y: CGFloat(height))
        ctx.scaleBy(x: scale, y: -scale) // page points, origin top-left
        ctx.translateBy(x: -crop.minX, y: -crop.minY)
        ctx.setLineCap(.round)
        ctx.setLineJoin(.round)

        let (rs, cs) = cells(in: crop)
        let text = CGMutablePath()
        for r in rs { for c in cs where c < rows[r].count { for s in strokes(r, c) { trace(s, into: text) } } }
        ctx.addPath(text)
        ctx.setStrokeColor(CGColor(red: 0.55, green: 0.55, blue: 0.55, alpha: 1))
        ctx.setLineWidth(glyphs.pen * Layout.em)
        ctx.strokePath()
        for mark in touching {
            if let ink = mark.ink {
                ctx.addPath(ink)
                ctx.setFillColor(mark.tool == .eraser ? CGColor(red: 0.9, green: 0.1, blue: 0.1, alpha: 0.45)
                                                      : CGColor(red: 0.1, green: 0.25, blue: 0.9, alpha: 1))
                ctx.fillPath()
                continue
            }
            let path = CGMutablePath()
            trace(mark.points, into: path)
            ctx.addPath(path)
            switch mark.tool {
            case .pen:
                ctx.setStrokeColor(CGColor(red: 0.1, green: 0.25, blue: 0.9, alpha: 1))
                ctx.setLineWidth(max(mark.width, glyphs.pen * Layout.em))
            case .eraser:
                ctx.setStrokeColor(CGColor(red: 0.9, green: 0.1, blue: 0.1, alpha: 0.45))
                ctx.setLineWidth(mark.width)
            }
            ctx.strokePath()
        }

        guard let image = ctx.makeImage() else { return nil }
        let data = NSMutableData()
        guard let dest = CGImageDestinationCreateWithData(data, UTType.png.identifier as CFString, 1, nil) else { return nil }
        CGImageDestinationAddImage(dest, image, nil)
        return CGImageDestinationFinalize(dest) ? data as Data : nil
    }
}

private func trace(_ stroke: [CGPoint], into path: CGMutablePath) {
    guard let first = stroke.first else { return }
    path.move(to: first)
    path.addLines(between: stroke.count > 1 ? stroke : [first, first])
}
