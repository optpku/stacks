/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_7_3_BaseChange

/-!
# Base change of quasi-compact morphisms of algebraic stacks

The base change of a quasi-compact morphism of algebraic stacks by any
morphism of algebraic stacks is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Lemma 101.7.3: The base change of a quasi-compact morphism of algebraic
stacks by any morphism of algebraic stacks is quasi-compact. -/
@[stacks 050V]
instance twoFibreProduct_snd {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [QuasiCompact f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    QuasiCompact (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
