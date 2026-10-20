/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.Lemma_101_33_7_ToBase
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap97.Theorem_97_17_2

/-!
# Smoothness of quotient stacks of group actions

If a group algebraic space `G` that is flat and locally of finite presentation
over `Y` acts on a smooth algebraic space `X` over `Y`, then the quotient stack
`[X / G]` is smooth over `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open GroupoidAlgebraicSpace GroupAlgebraicSpace
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Smooth

/-- Lemma 101.33.7: Let `X ⟶ Y` be a smooth morphism of algebraic spaces. Let `G`
be a group algebraic space over `Y` which is flat and locally of finite
presentation over `Y`. Let `G` act on `X` over `Y`. Then the quotient stack
`[X / G]` is smooth over `Y`. Formalized with `[X / G]` as
`(ofAction G X).quotientStack`, the structure morphism
`GroupoidAlgebraicSpace.toBase (ofAction G X)`, and `X ⟶ Y` as `X.X.hom`.
Smoothness of `G ⟶ Y` is not assumed. -/
@[stacks 0DLS, instance]
instance ofAction {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupAlgebraicSpace Y) (X : Action G)
    [AlgebraicSpace.Smooth X.X.hom] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    Smooth (GroupoidAlgebraicSpace.toBase (GroupoidAlgebraicSpace.ofAction G X)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Smooth
