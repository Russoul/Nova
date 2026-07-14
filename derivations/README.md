# derivations/

Each in-progress or completed Nova Foundation derivation lives in its own
subdirectory here:

```
derivations/<goal-name>/session.rules
derivations/<goal-name>/session.target
```

See the `derive` skill (`.claude/skills/derive/SKILL.md`) for the workflow
and command reference.

`./test.sh` (via `check-derivations.sh`) checks every `session.rules`/
`session.target` pair here with `nova-foundation-app check`, so a derivation
left in a broken state fails the test suite.
