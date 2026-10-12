/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_5_6_Square
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap100.Definition_100_8_1_Mono
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# Monomorphisms of algebraic stacks and inertia squares

If `f : X ⟶ Y` is a monomorphism of algebraic stacks, the square with vertices
`I_X`, `X`, `I_Y`, and `Y` is a 2-fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Inertia

/-- Lemma 101.5.6: Let `f : X ⟶ Y` be a monomorphism of algebraic stacks.
Then the diagram with vertices `I_X`, `X`, `I_Y`, and `Y`, horizontal legs
`Inertia.forget X` and `Inertia.forget Y`, and vertical legs `Inertia.map f`
and `f`, is a fibre product square. -/
@[stacks 06R5, instance]
instance mapForgetCone.isBilimit {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Mono f] :
    (mapForgetCone f).IsBilimit :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Inertia
