import Foundation

/// A rule the text names on a bar (`--- (el-trans)`): its name and the bar's row.
struct RuleName: Equatable {
    let name: String
    let row: Int
}

func ruleNames(of lines: [String]) -> [RuleName] {
    lines.enumerated().flatMap { r, line -> [RuleName] in
        guard rowKind(line) == .bar else { return [] }
        let formal = line.components(separatedBy: "//")[0]
        return formal.matches(of: #/\(([^)]*)\)/#).flatMap { m in
            m.output.1.split(whereSeparator: { $0 == "," || $0.isWhitespace }).map { RuleName(name: String($0), row: r) }
        }
    }
}

/// Words as speech gives them: lower case, hyphens and punctuation as spaces.
func spokenWords(_ s: String) -> [String] {
    let plain = String(s.lowercased().map { (c: Character) -> Character in c.isLetter || c.isNumber ? c : " " })
    return plain.split(separator: " ").map(String.init)
}

/// A word as it sounds: a letter said alone is written as one ("L") or as
/// its name ("el"); both become the name.
private func sounded(_ w: String) -> String {
    let names: [String: String] = ["b": "bee", "c": "see", "d": "dee", "f": "ef", "g": "gee", "j": "jay", "k": "kay",
                                   "l": "el", "m": "em", "n": "en", "p": "pee", "q": "cue", "r": "ar", "s": "es",
                                   "t": "tee", "v": "vee", "x": "ex", "z": "zed"]
    return names[w] ?? w
}

/// Words said around a target that do not name it.
private let filler: Set<String> = ["the", "a", "an", "of", "to", "in", "on", "for", "go", "goto", "jump", "show", "me",
                                   "please", "where", "is", "find", "section", "rule", "called", "named", "about", "at"]

/// How well a spoken phrase names a candidate, from 0 (not at all) to 1:
/// mostly the share of what was said (its filler aside) that the candidate
/// has, a word also counting when one begins the other ("subst" for
/// "substitution"); then, a little, the share of the candidate that was said,
/// so that of two candidates the one said more fully wins.
func match(_ phrase: String, _ candidate: String) -> Double {
    let said = spokenWords(phrase).filter { !filler.contains($0) }.map(sounded)
    let c = spokenWords(candidate).map(sounded)
    guard !said.isEmpty, !c.isEmpty else { return 0 }
    func meets(_ a: String, _ b: String) -> Bool { a == b || (min(a.count, b.count) >= 3 && (a.hasPrefix(b) || b.hasPrefix(a))) }
    let heard = Double(said.filter { w in c.contains { meets(w, $0) } }.count) / Double(said.count)
    let covered = Double(c.filter { w in said.contains { meets($0, w) } }.count) / Double(c.count)
    return 0.8 * heard + 0.2 * covered
}

/// Where a spoken target is, best first among: the headings, the rules, then
/// the lines that hold all its words (the first such line). Nil if nothing
/// matches well enough.
enum Found: Equatable {
    case heading(Heading)
    case rule(RuleName)
    case line(Int)

    var row: Int {
        switch self {
        case .heading(let h): h.row
        case .rule(let r): r.row
        case .line(let r): r
        }
    }
}

func find(_ phrase: String, in lines: [String], kind: FindKind = .anything) -> Found? {
    let heads = headings(of: lines), rules = ruleNames(of: lines)
    let bestHead = heads.map { ($0, match(phrase, $0.title)) }.max { $0.1 < $1.1 }
    let bestRule = rules.map { ($0, match(phrase, $0.name)) }.max { $0.1 < $1.1 }
    switch kind {
    case .section:
        return bestHead.flatMap { $0.1 >= 0.5 ? .heading($0.0) : nil }
    case .rule:
        return bestRule.flatMap { $0.1 >= 0.5 ? .rule($0.0) : nil }
    case .anything:
        let h = bestHead?.1 ?? 0, r = bestRule?.1 ?? 0
        if max(h, r) >= 0.75 { return r > h ? .rule(bestRule!.0) : .heading(bestHead!.0) }
        let words = spokenWords(phrase).filter { !filler.contains($0) }
        guard !words.isEmpty else { return nil }
        if let row = lines.indices.first(where: { r in let ws = spokenWords(lines[r]); return words.allSatisfy(ws.contains) }) {
            return .line(row)
        }
        if max(h, r) >= 0.5 { return r > h ? .rule(bestRule!.0) : .heading(bestHead!.0) }
        return nil
    }
}

enum FindKind { case section, rule, anything }
