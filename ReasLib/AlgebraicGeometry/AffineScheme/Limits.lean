/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Limits of affine schemes in locally ringed spaces

The canonical forgetful functor from affine schemes to locally ringed spaces
preserves all small limits; the finite-limit statement in Chapter 26 is an
immediate specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AffineScheme

/-- Limits of affine schemes are computed by the underlying locally ringed
spaces. -/
@[stacks 01I4, instance]
noncomputable instance forgetToLocallyRingedSpace_preservesLimits :
    PreservesLimits
      (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace) := sorry

#synth HasLimits AffineScheme.{u}
#synth PreservesLimits
  (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace)
#synth PreservesFiniteLimits
  (AffineScheme.forgetToScheme ⋙ Scheme.forgetToLocallyRingedSpace)

end AlgebraicGeometry.AffineScheme

namespace AlgebraicGeometry.SpecProduct

/-- The tensor-product spectrum, with its two canonical projections, as a
limiting binary fan. -/
@[stacks 01I4 "product cone of affine spectra"]
noncomputable def limitCone (R S : CommRingCat.{u}) :
    LimitCone (pair (Spec R) (Spec S)) where
  cone := ((CommRingCat.coproductCocone R S).op).map Scheme.Spec
  isLimit :=
    BinaryFan.isLimitMapConeEquiv
      (isLimitOfPreserves Scheme.Spec
        (BinaryCofan.IsColimit.op (CommRingCat.coproductCoconeIsColimit R S)))

end AlgebraicGeometry.SpecProduct

namespace AlgebraicGeometry

/-- Lemma 26.6.7: the categorical product of two affine spectra is the
spectrum of their tensor product over `ℤ`. -/
@[stacks 01I4 "product of affine spectra"]
noncomputable def prodSpecIso (R S : CommRingCat.{u}) :
    Spec R ⨯ Spec S ≅ Spec (CommRingCat.coproductCocone R S).pt :=
  limit.isoLimitCone (SpecProduct.limitCone R S)

/-- The first projection from the affine product is induced by the left
tensor-factor inclusion. -/
@[reassoc (attr := simp), stacks 01I4 "first projection from a product of affine spectra"]
theorem prodSpecIso_inv_fst (R S : CommRingCat.{u}) :
    (prodSpecIso R S).inv ≫ prod.fst =
      Spec.map (CommRingCat.coproductCocone R S).inl := sorry

/-- The second projection from the affine product is induced by the right
tensor-factor inclusion. -/
@[reassoc (attr := simp), stacks 01I4 "second projection from a product of affine spectra"]
theorem prodSpecIso_inv_snd (R S : CommRingCat.{u}) :
    (prodSpecIso R S).inv ≫ prod.snd =
      Spec.map (CommRingCat.coproductCocone R S).inr := sorry

end AlgebraicGeometry
