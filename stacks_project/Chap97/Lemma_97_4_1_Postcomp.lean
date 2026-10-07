module

public import stacks_project.Chap94.Definition_94_12_2_Etale

/-!
# Cancellation of étale 1-morphisms of groupoid fibrations along étale postcomposition

If a composite 1-morphism of categories fibred in groupoids is étale and the
second factor is étale, then the first factor is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom.Etale

/-- If a composite 1-morphism of categories fibred in groupoids is étale and
the second factor is étale, then the first factor is étale. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Etale (f ≫ g)] [Etale g] : Etale f := sorry

end AlgebraicGeometry.Groupoids.Hom.Etale
