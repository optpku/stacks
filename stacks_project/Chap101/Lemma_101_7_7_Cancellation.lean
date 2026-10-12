/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_4_1_Separation

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
