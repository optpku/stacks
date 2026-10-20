module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-!
# Cancellation of quasi-finiteness against quasi-separated quasi-DM postcomposition

If a composite morphism of algebraic stacks is quasi-finite and the second
factor is quasi-separated and quasi-DM, then the first factor is quasi-finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiFinite

/-- If a composite morphism of algebraic stacks is quasi-finite and the second
factor is quasi-separated and quasi-DM, then the first factor is quasi-finite. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiFinite (f ≫ g)] [QuasiSeparated g] [QuasiDM g] : QuasiFinite f := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiFinite
