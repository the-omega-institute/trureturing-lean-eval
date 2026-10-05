-- Vendored from kimihiro64/PrimeNumberTheoremAnd@0f15a38c PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
module

public import Mathlib.Algebra.Notation.Support

@[expose] public section

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
