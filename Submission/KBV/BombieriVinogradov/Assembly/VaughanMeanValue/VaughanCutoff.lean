-- Vendored from kimihiro64/bombieri-vinogradov@7a174830 BombieriVinogradov/Assembly/VaughanMeanValue/VaughanCutoff.lean (Apache-2.0)
-- Modified for the trureturing LeanEval submission (see NOTICE.md).
import Submission.KBV.BombieriVinogradov.Assembly.VaughanMeanValue.VaughanCutoff.Selection

/-!
# Vaughan cutoff interface

Stable aggregate import for the exhaustive source-scale cutoff theorem. The
selection module owns the four regime imports, keeping aggregate fan-out to one.
-/

set_option autoImplicit false
