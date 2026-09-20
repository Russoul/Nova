# The Agda side of each comparison

One file per part, with the Agda code that corresponds to the Nova
file of the same name. Each is written against the standard library
(`agda-stdlib`) or `--cubical` where marked. They are the
*counterparts* shown on the slide next to the Nova code; they are not
part of Nova's test suite and are not checked by `check.sh`. (No Agda
toolchain was available when this material was prepared, so read
them as illustrations of the well-known idioms — `subst`, `rewrite`,
`postulate funext`, setoids, bisimilarity records — rather than as
verified sources.)
