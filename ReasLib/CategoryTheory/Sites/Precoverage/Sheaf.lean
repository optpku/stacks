module

public import Mathlib.CategoryTheory.Sites.Precoverage
public import ReasLib.CategoryTheory.Sites.EqualizerSheafCondition

@[expose] public section

universe u v

open CategoryTheory.Limits

namespace CategoryTheory.Precoverage

/-- A Type-valued presheaf satisfies the sheaf condition for a precoverage when the
canonical restriction fork of every selected covering family is an equalizer. -/
def IsSheafOfTypes {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.HasPullbacks] (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ {B : C} {I : Type (max u v)}
    (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks],
    Presieve.ofArrows X π ∈ J B →
      Nonempty (IsLimit (Equalizer.Presieve.Arrows.fork P X π))

/-- For Type-valued presheaves in the aligned universe, the equalizer condition on every
selected covering family is equivalent to the sheaf condition for every covering presieve. -/
theorem isSheafOfTypes_iff_isSheafFor {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.HasPullbacks] (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsSheafOfTypes J P ↔
      ∀ {B : C} (R : Presieve B), R ∈ J B → R.IsSheafFor P := sorry

end CategoryTheory.Precoverage
