module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Complex.StrictlyPerfect.Local
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Locally strictly perfect complexes on the opens ringed site

This leaf compares the source-facing single-open-cover property on a ringed space with the
cover-wise localization property on its canonical opens ringed site.
-/

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex

variable {X : RingedSpace.{u}}

/-- The open-cover definition agrees with cover-wise local strict perfectness on the canonical
opens ringed site. -/
@[stacks 0FP9 "opens-ringed-site comparison"]
theorem isLocallyStrictlyPerfect_iff_opensRingedSite
    (E : _root_.CochainComplex (Modules X) ℤ) :
    IsLocallyStrictlyPerfect E ↔
      _root_.RingedSite.CochainComplex.IsLocallyStrictlyPerfect
        (X := opensRingedSite X) E := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex
