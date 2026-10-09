This is a small runtime mechanism fixture, not a Fermat submission.

`Submission.lean` embeds the unchanged 952-byte XZ/PAX fixture. Safe pure Lean
code decodes it; Lean's original frontend strictly compiles the original
`Fixture.ModuleA` and `Fixture.ModuleB` sources into the fixture's writable
`.lake`, preserving module headers, private names and dynamically defined
syntax. The entry imports these actual modules into the submitted environment.
`Submission.root` references `PackedB.root`, and the official fixture root in
`Solution.lean` references `Submission.root`. An additional submitted theorem
consumes the original imported tactic macro.

The archive also contains the actual original FLT `Submission.lean` as unchanged
material. This fixture does not elaborate it, and does not test or solve FLT.

`WorkspaceTest.lean` is the original official harness, SHA256
`17bd1978ec5ec46b151a616ae626d14cef01fcb6ce90a2d104dffae9a95e40df`.
It forces independent nanoda checking. The isolated Ubuntu workflow installs
the four original pinned tools and runs `lake test`; proof elaboration then
occurs inside original comparator `safeLakeBuild`, with project sources read
only and `.lake` writable. No archive tool, subprocess decoder, custom Lake
hook, proof axiom, trust bypass or modified judge is used.

Native fixture-only compilation, original exporter import and complete root
nanoda replay have already exited zero. The Ubuntu result must be judged from
its actual terminal receipt. This fixture contributes zero competition solves.
