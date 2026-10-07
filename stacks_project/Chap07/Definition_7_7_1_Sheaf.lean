module

public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import stacks_project.Chap07.Definition_7_6_2_Site

/-!
# Sheaves of types on a site

A Type-valued presheaf on a site with chosen covering families is a sheaf when
every covering `{Uᵢ ⟶ U}_{i ∈ I}` makes the restriction map the equalizer of
`pr₀*` and `pr₁*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Equalizer.Presieve

namespace CategoryTheory

namespace Precoverage

/-- A Type-valued presheaf on a site is a sheaf of types when, for every chosen
covering family `{Uᵢ ⟶ U}_{i ∈ I}`, the restriction map is the equalizer of
`pr₀*` and `pr₁*`. -/
def IsSheafOfTypes.{u, v} {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.IsSite] (P : Cᵒᵖ ⥤ Type (max u v)) : Prop :=
  ∀ {B : C} {I : Type (max u v)}
    (X : I → C) (π : (i : I) → X i ⟶ B)
    [(Presieve.ofArrows X π).HasPairwisePullbacks],
    Presieve.ofArrows X π ∈ J B →
      Nonempty (IsLimit (Fork.ofι (Arrows.forkMap P X π) (Arrows.w P X π)))

/-- At the aligned value universe `Type (max u v)`, the equalizer sheaf
condition on chosen covering families is equivalent to `IsSheafFor` on every
covering presieve. -/
theorem isSheafOfTypes_iff_isSheafFor.{u, v} {C : Type u} [Category.{v} C]
    (J : Precoverage C) [J.IsSite] (P : Cᵒᵖ ⥤ Type (max u v)) :
    IsSheafOfTypes J P ↔
      ∀ {B : C} (R : Presieve B), R ∈ J B → R.IsSheafFor P :=
  sorry

end Precoverage

end CategoryTheory
