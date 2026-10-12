/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation
public import stacks_project.Chap101.Definition_101_37_1_FiniteType
public import stacks_project.Chap106.Lemma_106_9_1_Pullback

/-!
# Flattening morphisms of algebraic stacks by admissible blowups

A finite-type quasi-separated morphism from an algebraic stack to a qcqs
algebraic space that is already flat and locally of finite presentation over a
quasi-compact open becomes flat and of finite presentation after a
`V`-admissible blowup, on a closed substack of the base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.9.1. Let `f : X ⟶ Y` be a morphism from an algebraic stack to an
algebraic space. Let `V ⊂ Y` be an open subspace. Assume `Y` is quasi-compact
and quasi-separated, `f` is of finite type and quasi-separated, `V` is
quasi-compact, and `X_V` is flat and locally of finite presentation over `V`.
Then there exists a `V`-admissible blowup `Y' ⟶ Y` and a closed substack
`X' ⊂ X_{Y'}` with `X'_V = X_V` such that `X' ⟶ Y'` is flat and of finite
presentation.

Here `X_V` is `pullback f V.ι` with structure map `pullbackSnd f V.ι`,
`X_{Y'}` is `pullback f b`, `V'` is `V.inverseImage b`, and `X'_V = X_V` is
`ClosedSubstack.restrictsToOpen f b V X'` (the closed immersion becomes an
isomorphism on the open fibre). The structure map `X' ⟶ Y'` is
`X'.ι ≫ pullbackSnd f b`. -/
@[stacks 0CQ4]
theorem exists_isAdmissibleBlowup_flat_finitePresentation
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.QuasiSeparated f]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    [AlgebraicStack.Flat (pullbackSnd f V.ι)]
    [AlgebraicStack.LocallyOfFinitePresentation (pullbackSnd f V.ι)] :
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y) (X' : ClosedSubstack (pullback f b)),
      AlgebraicSpace.IsAdmissibleBlowup V b ∧
        ClosedSubstack.restrictsToOpen f b V X' ∧
        AlgebraicStack.Flat (X'.ι ≫ pullbackSnd f b) ∧
          AlgebraicStack.FinitePresentation (X'.ι ≫ pullbackSnd f b) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
