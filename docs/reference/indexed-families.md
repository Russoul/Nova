# Indexed families
%stub

Types indexed by values — the payoff, and the classic example.

## Vectors

- `V : ℕ → U` is not one type but a family, one per length.
- Constructors that fix their index: `vnil` at `Z`, `vcons` at `S n`.
- Two ways to get there: an indexed `data` sort, or a function
  computing a type by recursion.

## Programming with an index

- Functions whose types track the length: append, map, head-of-nonempty.
- The index is checked, so a length error is a type error.

## Eliminating

- The motive now mentions the index, and the eliminator takes the
  index spine before the scrutinee.

## The awkward part, and Nova's answer

- `vappend`'s result is at length `n + m`, but the recursion produces
  `Z + m` — different spellings of the same number.
- In other systems this is repaired with a cast **inside the type**. In
  Nova it is not repaired at all, because the two types are already
  equal; see [Types without coherence](#coherence).
