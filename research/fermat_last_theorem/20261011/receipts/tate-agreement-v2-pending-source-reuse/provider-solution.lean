theorem solution
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [AlgebraicCurve.IsCurveOver K L] [PerfectField K]
    [∀ u : AlgebraicCurve.Place K L, u.FiniteResidue]
    (hfin : ModularCurve.KwF4gRRTate.KwF4gRRTateCommFinite K L) :
    ModularCurve.KwF4gRRTate.KwF4gRRTateAgreement K L hfin :=
  ModularCurve.KwF4gRRTate.kwF4gRRTate_agreement_of_kernelData hfin
    ModularCurve.KwTateRR3.kwTateRR3_cohenKernelDataExists
