import CoreGraphics
import Foundation

/// A pen's track: where the tip was, and the ink's radius there (from the
/// Pencil's pressure).
struct InkSample {
    var point: CGPoint
    var radius: CGFloat
}

/// A pen's radius for a Pencil pressure (force / its maximum, 0...1): a light
/// touch draws a fine line, a firm one up to about three times as wide.
func inkRadius(base: CGFloat, pressure: CGFloat) -> CGFloat {
    base * (0.55 + 1.1 * pow(min(max(pressure, 0), 1), 0.7))
}

/// How many times over a pen stroke is smoothed until the slider says otherwise.
let defaultSmoothing: CGFloat = 3

/// The samples as the ink is drawn from: those too close to the one before
/// dropped (they carry no direction), and the rest smoothed with their
/// neighbours (weights 1-2-1, the ends kept where the pen touched and lifted),
/// `strength` times over: 1 takes out the tip's jitter, more rounds the
/// writing off further; a fraction makes the last pass part-way.
func smoothed(_ samples: [InkSample], strength: CGFloat = defaultSmoothing) -> [InkSample] {
    var kept = [InkSample]()
    for s in samples {
        if let last = kept.last, hypot(s.point.x - last.point.x, s.point.y - last.point.y) < 0.3 {
            kept[kept.count - 1].radius = max(last.radius, s.radius)
        } else {
            kept.append(s)
        }
    }
    guard kept.count > 2, strength > 0 else { return kept }
    var out = kept
    for pass in 0..<Int(strength.rounded(.up)) {
        let w = min(1, strength - CGFloat(pass)), before = out
        for i in 1..<(before.count - 1) {
            let (a, b, c) = (before[i - 1], before[i], before[i + 1])
            let x = (a.point.x + 2 * b.point.x + c.point.x) / 4, y = (a.point.y + 2 * b.point.y + c.point.y) / 4
            let r = (a.radius + 2 * b.radius + c.radius) / 4
            out[i] = InkSample(point: CGPoint(x: b.point.x + w * (x - b.point.x), y: b.point.y + w * (y - b.point.y)),
                               radius: b.radius + w * (r - b.radius))
        }
    }
    return out
}

/// The ink of a stroke as a shape to fill: its left edge as a smooth curve, a
/// round end, its right edge back, a round start. One sample is a dot.
func inkOutline(_ samples: [InkSample]) -> CGPath {
    let path = CGMutablePath()
    guard let first = samples.first else { return path }
    if samples.count == 1 {
        path.addEllipse(in: CGRect(x: first.point.x - first.radius, y: first.point.y - first.radius,
                                   width: 2 * first.radius, height: 2 * first.radius))
        return path
    }
    // The direction of travel at each sample, and the normal to its left.
    let n = samples.count
    var tangents = [CGVector](), lefts = [CGPoint](), rights = [CGPoint]()
    for i in 0..<n {
        let a = samples[max(i - 1, 0)].point, b = samples[min(i + 1, n - 1)].point
        var t = CGVector(dx: b.x - a.x, dy: b.y - a.y)
        let len = hypot(t.dx, t.dy)
        t = len > 0 ? CGVector(dx: t.dx / len, dy: t.dy / len) : (tangents.last ?? CGVector(dx: 1, dy: 0))
        tangents.append(t)
        let (p, r) = (samples[i].point, samples[i].radius)
        lefts.append(CGPoint(x: p.x - t.dy * r, y: p.y + t.dx * r))
        rights.append(CGPoint(x: p.x + t.dy * r, y: p.y - t.dx * r))
    }
    // A half circle around p, from one side through the way t points to the other.
    func cap(_ p: CGPoint, _ r: CGFloat, from side: CGVector, through t: CGVector) -> [CGPoint] {
        (1...8).map { k in
            let phi = CGFloat(k) * .pi / 8
            return CGPoint(x: p.x + r * (side.dx * cos(phi) + t.dx * sin(phi)), y: p.y + r * (side.dy * cos(phi) + t.dy * sin(phi)))
        }
    }
    // A curve through the midpoints of a run of points, each point its control.
    func curve(_ ps: [CGPoint]) {
        for i in 1..<(ps.count - 1) {
            path.addQuadCurve(to: CGPoint(x: (ps[i].x + ps[i + 1].x) / 2, y: (ps[i].y + ps[i + 1].y) / 2), control: ps[i])
        }
        path.addLine(to: ps[ps.count - 1])
    }
    let end = samples[n - 1], tEnd = tangents[n - 1], tStart = tangents[0]
    // One closed piece: addLines(between:) would start a new one at each cap.
    path.move(to: lefts[0])
    curve(lefts)
    cap(end.point, end.radius, from: CGVector(dx: -tEnd.dy, dy: tEnd.dx), through: tEnd).forEach { path.addLine(to: $0) }
    curve(rights.reversed())
    cap(first.point, first.radius, from: CGVector(dx: tStart.dy, dy: -tStart.dx),
        through: CGVector(dx: -tStart.dx, dy: -tStart.dy)).forEach { path.addLine(to: $0) }
    path.closeSubpath()
    return path
}
