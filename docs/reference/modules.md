# Modules and imports
%stub

How files find each other, and how names resolve.

## Module names

- A dotted name (`Data.Nat`) mapping to a path.

## `import`

- `import M` makes `M`'s names available qualified.
- `import M (a, b)` opens `a` and `b` unqualified — and brings their
  fixities with them.

## Qualified names

- `nat.plusComm`; when a qualified name is required, and how `using`
  clauses spell lemma names.

## The module closure

- Loading deduplicates by module name, so `all.nova` checks the corpus
  in one run.
- The lemma store is scoped to a module's import closure: a module
  elaborates the same standalone as it does inside a batch.

## Name resolution

- Resolution happens **before** elaboration: names become de Bruijn
  indices and survive only as display metadata. The elaborator never
  consults a name; the report printer does.
