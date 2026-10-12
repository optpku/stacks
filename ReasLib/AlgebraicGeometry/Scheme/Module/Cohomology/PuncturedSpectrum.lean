/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.InjectiveHull

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An étale quasi-compact scheme over a regular local ring containing a field is affine
if it avoids the closed point, is affine over the punctured spectrum, and its structure-sheaf
cohomology vanishes in every degree at least `(ringKrullDim A).unbotD 0 - 1`. -/
theorem isAffine_of_cohomology_isZero
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [IsRegularLocalRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (CommRingCat.of A)) [Etale f] [QuasiCompact f]
    (h_m : IsLocalRing.closedPoint A ∉ Set.range f)
    (g : V ⟶ PuncturedSpectrum.scheme A) [IsAffineHom g]
    (h_factor : g ≫ (PuncturedSpectrum.puncturedOpen A).ι = f)
    (h_vanish : ∀ i : ℕ, (ringKrullDim A).unbotD 0 - 1 ≤ (i : ℕ∞) →
      IsZero (Scheme.Hom.cohomology f
        (SheafOfModules.unit V.ringCatSheaf : V.Modules) i)) :
    IsAffine V := sorry

end AlgebraicGeometry.Scheme.Hom
