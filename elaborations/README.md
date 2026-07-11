# elaborations/

Each finished Nova Foundation elaboration lives in its own subdirectory
here:

```
elaborations/<goal-name>/<name>.sig
```

A `.sig` file is a surface Σ program (`Nova.Foundation.Elaboration`'s
proof-term syntax, one `- <SigEntry>` per line) that elaborates directly
into a well-formed low-level `Sig` via:

```
nova-foundation-app elaborate <file>
```

This bypasses `Nova.Foundation.Derivation`'s `TypingRule`/`Truth` machinery
entirely — unlike `derivations/`, there's no separate target file, since
each entry's own declared type already states the fact it establishes.
