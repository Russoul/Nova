import Foundation

/// What a stretch of a line is, as the checker reads it: the token kinds of
/// tools/nspec.lua (`M.colours` gives each a colour).
enum TokenKind: String {
    case heading, prose, bar, rule, keyword, nova, level, index, tos, proof
}

/// A token: bytes `from...to` of its line (UTF-8, from 1, inclusive), and
/// what they are. Of a line's tokens, a later one wins where they overlap.
struct Token: Equatable {
    let from: Int
    let to: Int
    let kind: TokenKind
}

/// Tokens as the relay sends them: `[[from, to, kind], ...]` for one line.
/// A kind this app does not know is skipped (drawn plain).
func parseTokens(_ value: Any?) -> [Token] {
    (value as? [[Any]] ?? []).compactMap { t in
        guard t.count == 3, let from = t[0] as? Int, let to = t[1] as? Int,
              let name = t[2] as? String, let kind = TokenKind(rawValue: name) else { return nil }
        return Token(from: from, to: to, kind: kind)
    }
}

/// The kind of each cell of a line (a character with its marks): the kind of
/// the last token over the cell's first byte, or nil.
func cellKinds(_ line: String, _ tokens: [Token]) -> [TokenKind?] {
    var starts = [Int](), byte = 1
    for ch in line {
        starts.append(byte)
        byte += ch.utf8.count
    }
    var kinds = [TokenKind?](repeating: nil, count: starts.count)
    for t in tokens {
        for (i, b) in starts.enumerated() where t.from <= b && b <= t.to { kinds[i] = t.kind }
    }
    return kinds
}

/// The tokens after an edit: the replaced lines' tokens dropped (the new
/// lines have none yet), the rest moved with the text, then each line the
/// relay sent (numbered in the new text) taking its tokens from it.
func movingTokens(_ rows: [[Token]], after replacements: [Replacement], delta: [Int: [Token]]) -> [[Token]] {
    var out = rows
    for r in replacements.sorted(by: { $0.first > $1.first }) {
        out.replaceSubrange(r.first..<(r.last + 1), with: Array(repeating: [], count: r.lines.count))
    }
    for (row, ts) in delta where out.indices.contains(row) { out[row] = ts }
    return out
}
