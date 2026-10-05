-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Proof/SiegelWalfisz/ExplicitFormula/Residue/Poles/LogDerivativeSimple.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Meromorphic.LFunction
import Submission.KBV.BombieriVinogradov.Proof.SiegelWalfisz.ExplicitFormula.Residue.Poles.LFunctionFiniteOrder
import Submission.PNT.PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-!
# Simple poles of the Dirichlet L-function logarithmic derivative

This module applies the finite-order logarithmic-derivative theorem on an
arbitrary set.
-/

set_option autoImplicit false

noncomputable section

namespace BombieriVinogradov.SiegelWalfisz

/-- The logarithmic derivative of a nonprincipal Dirichlet L-function has at
most simple poles on every set. Multiplicities of L-function zeros appear in
the residues, not in the pole orders of the logarithmic derivative. -/
theorem hasSimplePolesOn_logDeriv_LFunction
    {N : Nat} [NeZero N] {chi : DirichletCharacter Complex N}
    (hchi : Ne chi 1) (U : Set Complex) :
    HasSimplePolesOn (logDeriv chi.LFunction) U :=
  logDeriv_hasSimplePolesOn_of_meromorphicOrderAt_ne_top
    (meromorphic_LFunction_of_ne_one hchi).meromorphicOn
    (meromorphic_logDeriv_LFunction hchi).meromorphicOn
    (fun p _ => meromorphicOrderAt_LFunction_ne_top hchi p)

end BombieriVinogradov.SiegelWalfisz
