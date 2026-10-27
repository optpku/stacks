/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap101.Lemma_101_33_7_ToBase
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap97.Theorem_97_17_2
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.SmallAction
import StacksCheckRecall

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

/- Lemma 101.33.7: a flat, locally finitely presented group acting on a smooth
algebraic space has a quotient stack smooth over the base. -/
@[stacks 0DLS] #check (AlgebraicGeometry.AlgebraicStack.Smooth.ofAction :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (G : GroupAlgebraicSpace Y) (X : Action G)
    [AlgebraicSpace.Smooth X.X.hom] [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom],
    -- Local instance justification (defeq pin): the algebraic-stack smoothness predicate is indexed by the proved algebraicity of this concrete quotient; the explicit action cannot have a companion instance.
    letI : AlgebraicStack (SmallQuotient.quotientStack (GroupoidAlgebraicSpace.ofAction G X)) :=
      isAlgebraicStack_quotientStack_of_flat (GroupoidAlgebraicSpace.ofAction G X)
        (SmallQuotient.flat_ofAction G X) (SmallQuotient.locallyOfFinitePresentation_ofAction G X)
    Smooth (SmallQuotient.toBase (GroupoidAlgebraicSpace.ofAction G X)))

end AlgebraicGeometry.AlgebraicStack.Smooth
