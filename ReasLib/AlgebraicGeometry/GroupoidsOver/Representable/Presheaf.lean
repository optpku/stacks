module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable

/-!
# Representability of presheaf morphisms and their groupoid fibrations

A morphism of set-valued presheaves is representable by algebraic spaces if and
only if its associated morphism of categories fibred in groupoids is.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A morphism of set-valued presheaves on schemes over `S` is representable by
algebraic spaces if and only if its canonical associated morphism of categories
fibred in sets, viewed in groupoids, is representable by algebraic spaces. -/
@[stacks 0458]
theorem relativelyRepresentableByAlgebraicSpaces.iff_ofPresheaf
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    AlgebraicSpace.representableByAlgebraicSpaces a ↔
      relativelyRepresentableByAlgebraicSpaces
        ((Sets.toGroupoids (Over S)).map ((Sets.ofPresheaf (Over S)).map a)) := sorry

end AlgebraicGeometry
