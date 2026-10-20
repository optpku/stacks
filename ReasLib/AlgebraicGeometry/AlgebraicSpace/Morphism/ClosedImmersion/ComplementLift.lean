module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Lifting morphisms to open complements -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A map into `X` that misses `|Z|` factors through the open complement of a
closed immersion `i : Z ⟶ X`, via the missing-closed-image subfunctor. -/
noncomputable def closedImmersionComplementLift {T X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (α : T ⟶ X)
    (h : ∀ (U : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj U),
      missesClosedImage i (α.app U t)) :
    T ⟶ closedImmersionComplement i where
  app U := TypeCat.ofHom fun t ↦ ⟨α.app U t, h U t⟩
  naturality := sorry

/-- The lifted map to the complement composes to the original map into `X`. -/
theorem closedImmersionComplementLift_comp {T X Z : AlgebraicSpace S}
    (i : Z ⟶ X) [IsClosedImmersion i] (α : T ⟶ X)
    (h : ∀ (U : (Over S)ᵒᵖ) (t : T.functorOfPoints.obj U),
      missesClosedImage i (α.app U t)) :
    closedImmersionComplementLift i α h ≫ closedImmersionComplementι i = α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
