# Nova

Nova Foundation is a mechanised formal type theory based on
[extensional Martin Lof Type Theory](https://ncatlab.org/nlab/show/extensional+type+theory),
checked by an elaborator/kernel pipeline: surface files elaborate to
certificate-carrying artifacts that a small trusted kernel re-checks.
Written in [Idris2](https://github.com/idris-lang/Idris2).

See `docs/NovaFoundation.txt` for the theory, `docs/NovaPipeline.txt`
for the architecture, `docs/NovaElaboration.txt` for the surface
syntax and elaborator, and `docs/NovaKernel.txt` for the kernel rules.

### Dependencies

[Just-a-Parser](https://github.com/Russoul/Just-a-Parser)
