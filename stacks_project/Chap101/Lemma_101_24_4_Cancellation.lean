/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_24_1_QuasiFinite
public import stacks_project.Chap101.Definition_101_4_1_Separation

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
