/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import ReasLib.RingTheory.DividedPowers.Localization

@[expose] public section

open AlgebraicGeometry

namespace DividedPowers

universe u

variable {R : Type u} [CommRing R] {I : Ideal R} (γ : DividedPowers I)

/-- The quasi-coherent ideal on the affine spectrum associated to `I`. -/
noncomputable def affineIdeal : (Spec (.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.comap (Scheme.ΓSpecIso (.of R)).hom.hom)

/-- Applying divided powers pointwise to a section of the affine ideal is
locally a fraction, so defines a section of the structure sheaf. -/
theorem affineDpow_isLocallyFraction (U : (Spec (.of R)).affineOpens)
    (n : ℕ) (f : Γ(Spec (.of R), U)) (hf : f ∈ (affineIdeal (I := I)).ideal U) :
    (StructureSheaf.isLocallyFraction R R).pred
      (fun x : U.1 ↦ localizationDpow γ x.1.asIdeal.primeCompl
        (StructureSheaf.Localizations R x.1) n (f.1 x)) := sorry

/-- The actual divided-power operation on affine sections: apply the fraction
formula in each local ring. Only local representability is proof data. -/
noncomputable def affineDpow (U : (Spec (.of R)).affineOpens)
    (n : ℕ) (f : Γ(Spec (.of R), U)) : Γ(Spec (.of R), U) :=
  open scoped Classical in
  if hf : f ∈ (affineIdeal (I := I)).ideal U then
    ⟨fun x ↦ localizationDpow γ x.1.asIdeal.primeCompl
      (StructureSheaf.Localizations R x.1) n (f.1 x),
      affineDpow_isLocallyFraction γ U n f hf⟩
  else 0

/-- On an ideal section the construction has exactly the localized pointwise
formula, independently of the proof that it is locally representable. -/
theorem affineDpow_apply (U : (Spec (.of R)).affineOpens) (n : ℕ)
    (f : Γ(Spec (.of R), U)) (hf : f ∈ (affineIdeal (I := I)).ideal U)
    (x : U.1) :
    (affineDpow γ U n f).1 x =
      localizationDpow γ x.1.asIdeal.primeCompl
        (StructureSheaf.Localizations R x.1) n (f.1 x) := by
  classical
  simp only [affineDpow, dif_pos hf]

/-- The divided-power structure on each affine open of the spectrum. -/
noncomputable def affine (U : (Spec (.of R)).affineOpens) :
    DividedPowers ((affineIdeal (I := I)).ideal U) where
  dpow := affineDpow γ U
  dpow_null := by
    classical
    intro n x hx
    simp only [affineDpow, dif_neg hx]
  dpow_zero := sorry
  dpow_one := sorry
  dpow_mem := sorry
  dpow_add := sorry
  dpow_mul := sorry
  mul_dpow := sorry
  dpow_comp := sorry

/-- Restriction to an affine basic open preserves the pointwise divided powers. -/
theorem affine_compatible (U : (Spec (.of R)).affineOpens)
    (f : Γ(Spec (.of R), U)) :
    IsDPMorphism (affine γ U) (affine γ ((Spec (.of R)).affineBasicOpen f))
      ((Spec (.of R)).presheaf.map
        (CategoryTheory.homOfLE ((Spec (.of R)).basicOpen_le f)).op).hom := sorry

end DividedPowers
