module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The basic open `D(2)` in `Spec ℤ`

This file records the affine pair `Spec ℤ` and `Spec (Localization.Away (2 : ℤ))`,
the open immersion of the latter onto `D(2)`, and the inverse map from that open
subscheme, which does not extend along the open-subscheme inclusion.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.AwayTwo

/-- The affine scheme `Spec ℤ`. -/
abbrev source : Scheme :=
  Spec (CommRingCat.of ℤ)

/-- The affine scheme `Spec (Localization.Away (2 : ℤ))`. -/
abbrev target : Scheme :=
  Spec (CommRingCat.of (Localization.Away (2 : ℤ)))

/-- The canonical open immersion `Spec (Localization.Away (2 : ℤ)) ⟶ Spec ℤ`. -/
abbrev inclusion : target ⟶ source :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ))))

/-- The open subscheme `D(2) ⊆ Spec ℤ`, as the image of `inclusion`. -/
abbrev openSubscheme : source.Opens :=
  inclusion.opensRange

/-- The inverse of `inclusion` as a morphism from the open subscheme to `target`. -/
def morphism : openSubscheme.toScheme ⟶ target :=
  inclusion.isoOpensRange.inv

/-- `source` is affine. -/
instance instIsAffineSource : IsAffine source := inferInstance

/-- `target` is affine. -/
instance instIsAffineTarget : IsAffine target := inferInstance

/-- The chosen map from the open subscheme is a section of `inclusion`. -/
theorem morphism_comp_inclusion : morphism ≫ inclusion = openSubscheme.ι := sorry

/-- There is no ring homomorphism from `Localization.Away (2 : ℤ)` to `ℤ`. -/
theorem not_exists_ringHom : ¬ Nonempty (Localization.Away (2 : ℤ) →+* ℤ) := sorry

/-- The morphism `openSubscheme ⟶ target` does not extend along `openSubscheme.ι`. -/
theorem morphism_not_extends :
    ¬ ∃ g : source ⟶ target, openSubscheme.ι ≫ g = morphism := sorry

end AlgebraicGeometry.AwayTwo
