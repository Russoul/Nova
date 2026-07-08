* Use `pack` to type check / build / run idris2 programs
* Use `./test.sh` to run the test suite (passes the required `PATH_TO_SELF` argument automatically); extra golden framework flags (e.g. `--only add`) can be appended
* To synthesize or check a Nova Foundation derivation (`.rules`/`.target` files, `ctx-wf`/`el-wf`/... judgements), use the `derive` skill instead of reading the Idris sources cold
