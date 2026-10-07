module

public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite

/-!
# Cancellation of local quasi-finiteness against quasi-DM postcomposition

If a composite morphism of algebraic stacks is locally quasi-finite and the
second factor is quasi-DM, then the first factor is locally quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite

/-- If a composite morphism of algebraic stacks is locally quasi-finite and the
second factor is quasi-DM, then the first factor is locally quasi-finite. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyQuasiFinite (f ≫ g)] [QuasiDM g] : LocallyQuasiFinite f := sorry

end AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
