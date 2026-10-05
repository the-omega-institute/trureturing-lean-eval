-- Vendored from AxiomMath/PrimeGapsLib@1faa7b14 PrimeGapsCert/Gap246/LHS/ScalarDefs.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Submission.PGL.PrimeGapsCert.Gap246.Kernel.LHSScalar
public import Submission.PGL.PrimeGapsCert.Gap246.LHS.Defs

import Submission.PGL.PrimeGapsCert.Gap246.Sparse.DataCommands

/-! # Auxiliary scalar checks for the packed sparse LHS certificate -/

set_option maxRecDepth 100000 in
cert246Data_emit_lhs_scalar_checks
