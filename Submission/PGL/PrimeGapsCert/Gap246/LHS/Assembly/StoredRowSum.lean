-- Vendored from AxiomMath/PrimeGapsLib@1faa7b14 PrimeGapsCert/Gap246/LHS/Assembly/StoredRowSum.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Submission.PGL.PrimeGapsCert.Gap246.LHS.Assembly.RowSum
public import Submission.PGL.PrimeGapsCert.Gap246.LHS.Assembly.RowsComplete

/-! # Sum of the stored packed sparse LHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- The stored LHS row totals sum to the complete symmetric LHS quadratic form. -/
theorem certLhsStoredRowSum :
    (∑ row : Fin 138, certLhsStoredRow row) =
      preEpsWitnessInt.lhsPairWithTablesSumSymmetric certFactorTables := by
  simpa only [certLhsRows_complete] using certLhsRowSum

end PrimeGaps.Gap246
