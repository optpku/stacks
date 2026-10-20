module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Variety
public import ReasLib.RingTheory.MvPolynomial.PthPowerHypersurface

/-!
# A p-th-power hypersurface with nonreduced field extension

This file packages the rational-function-plane p-th-power hypersurface as a
scheme over its coefficient field and records the failure of reducedness after
adjoining roots of its two coefficients.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane

open MvPolynomial.PthPowerHypersurface.RationalFunctionPlane

/-- The affine scheme defined over the two-variable rational function field by
`1 + s X₀^p + t X₁^p = 0`. -/
def scheme (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (baseRing p))

/-- The structure morphism from the p-th-power hypersurface to the spectrum of
its rational function field. -/
def toBase (p : ℕ) [Fact p.Prime] :
    scheme p ⟶ Spec (CommRingCat.of (BaseField p)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) (baseRing p)))

/-- The p-th-power hypersurface as a scheme over its rational function field. -/
def overBase (p : ℕ) [Fact p.Prime] :
    Over (Spec (CommRingCat.of (BaseField p))) :=
  Over.mk (toBase p)

/-- The rational-function-plane p-th-power hypersurface is a variety over its
coefficient field. -/
instance instVariety (p : ℕ) [Fact p.Prime] : Variety (overBase p) := sorry

/-- The scheme obtained by pulling the p-th-power hypersurface back along a
field extension. -/
def baseChange (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L]
    [Algebra (BaseField p) L] :
    Scheme :=
  pullback (toBase p)
    (Spec.map (CommRingCat.ofHom (algebraMap (BaseField p) L)))

/-- If both coordinate rational functions acquire p-th roots in a field
extension, the corresponding scheme-theoretic base change is not reduced. -/
theorem baseChange_not_isReduced (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L]
    [Algebra (BaseField p) L]
    (ha : ∃ a : L, a ^ p = algebraMap (BaseField p) L (s p))
    (hb : ∃ b : L, b ^ p = algebraMap (BaseField p) L (t p)) :
    ¬ IsReduced (baseChange p L) := sorry

end AlgebraicGeometry.PthPowerHypersurface.RationalFunctionPlane
