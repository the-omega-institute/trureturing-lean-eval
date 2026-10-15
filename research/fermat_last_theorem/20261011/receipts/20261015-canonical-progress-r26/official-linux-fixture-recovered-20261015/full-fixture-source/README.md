This source-only fixture tests the production boundary of an original packed
module named Submission inside the submitted outer module also named Submission.
The original packed 655-byte root source is passed byte-for-byte to Lean's
runFrontend at strict trust 0 with oleanFileName? = none. Its entire checked
environment is installed as the current root environment. The outer compiler
writes the final Submission.olean, using the original header imports, original
module-specific private proof and original macro persistent extensions.

The checked root is Submission.fermat_last_theorem : forall n : Nat, n = n.
This is explicitly a toy fixture; it does not elaborate or prove the actual
Fermat theorem. The real original FLT Submission.lean is only archive material.

Solution.lean consumes the final root and both the root's own original macro and
its imported module's macro. Official WorkspaceTest.lean is unchanged and forces
nanoda. The isolated Ubuntu carrier retains original comparator, landrun,
lean4export and nanoda source pins and runs the full original lake test chain.
The loader performs no self import and emits no intermediate root olean.

Native frontend, final exporter and full fixture root nanoda have exited zero.
Actual Ubuntu acceptance must be read from its new terminal receipt; old
fixture acceptance does not stand in for this new boundary. Official competition
solve credit remains zero, and full original FLT continues with its sole owner.
