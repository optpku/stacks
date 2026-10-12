/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact

/-!
# Base change of quasi-compact morphisms of algebraic stacks

Quasi-compact morphisms of algebraic stacks remain quasi-compact along the
second projection of any bilimit 2-fibre product cone, and along the first
projection of a chosen 2-fibre product when that leg is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Quasi-compact morphisms of algebraic stacks remain quasi-compact along the
second projection of any bilimit `PseudoPullbackCone`. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y} [QuasiCompact f]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    QuasiCompact c.snd := sorry

/-- The first projection of a chosen 2-fibre product is quasi-compact whenever
the second leg is a quasi-compact morphism of algebraic stacks. -/
instance twoFibreProduct_fst {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact g]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    QuasiCompact (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) := sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
