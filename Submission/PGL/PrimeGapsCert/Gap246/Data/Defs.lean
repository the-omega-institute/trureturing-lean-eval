-- Vendored from AxiomMath/PrimeGapsLib@1faa7b14 PrimeGapsCert/Gap246/Data/Defs.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Submission.PGL.PrimeGapsCert.Gap246.Data.Packed
public import Submission.PGL.PrimeGapsCert.Gap246.Kernel.Extra
public import Submission.PGL.PrimeGapsCert.Gap246.Kernel.Moments

import Submission.PGL.PrimeGapsCert.Gap246.Emit.Commands

/-! # Dependency-isolated shared data for the packed certificate -/

set_option maxRecDepth 100000 in
cert246Data_emit_shared_checks
