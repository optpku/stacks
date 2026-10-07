module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
public import ReasLib.CategoryTheory.Limits.Shapes.Cofork.BaseChange
public import ReasLib.CategoryTheory.Sites.Family.Overlap.Basic

/-!
# Coequalizers local for fpqc coverings

This module records a criterion for a cofork of schemes to be colimiting when that property holds
after base change to every member and every pairwise overlap of an fpqc covering family.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Scheme.FpqcCovering

/-- A cofork of schemes is colimiting if its base changes to every member and every pairwise
overlap of an fpqc covering family are colimiting. -/
theorem isColimit_of_baseChange {X Y Z : Scheme.{u}} (a b : X ⟶ Y) (c : Y ⟶ Z)
    (h : a ≫ c = b ≫ c) (𝒰 : SemiRepresentableFamily.Over.{v} Z)
    (h𝒰 : Scheme.FpqcCovering 𝒰.obj)
    (h_member : ∀ i : 𝒰.index,
      Nonempty (IsColimit ((Cofork.ofπ c h).baseChange (𝒰.obj i).hom)))
    (h_overlap : ∀ i j : 𝒰.index,
      Nonempty (IsColimit ((Cofork.ofπ c h).baseChange (𝒰.overlapMap i j)))) :
    Nonempty (IsColimit (Cofork.ofπ c h)) := sorry

end AlgebraicGeometry.Scheme.FpqcCovering
