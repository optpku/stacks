module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation

/-!
# Cancellation of quasi-compactness against quasi-separated postcomposition

If a composite morphism of algebraic stacks is quasi-compact and the second
factor is quasi-separated, then the first factor is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- If a composite morphism of algebraic stacks is quasi-compact and the second
factor is quasi-separated, then the first factor is quasi-compact. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact (f ≫ g)] [QuasiSeparated g] : QuasiCompact f := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
