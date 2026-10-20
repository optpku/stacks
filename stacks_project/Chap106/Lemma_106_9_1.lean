/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Flat.Blowup

/-!
# Flattening morphisms of algebraic stacks by admissible blowups
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 106.9.1. Let `f : X ⟶ Y` be a morphism from an algebraic stack to an
algebraic space. Let `V ⊂ Y` be an open subspace. Assume `Y` is quasi-compact
and quasi-separated, `f` is of finite type and quasi-separated, `V` is
quasi-compact, and `X_V` is flat and locally of finite presentation over `V`.
Then there exists a `V`-admissible blowup `Y' ⟶ Y` and a closed substack
`X' ⊂ X_{Y'}` with `X'_V = X_V` such that `X' ⟶ Y'` is flat and of finite
presentation.

The closed substack is represented by a closed replete object property and
its canonical inclusion. Agreement over the open means equivalence over the
base of the canonical restriction projection. -/
@[stacks 0CQ4]
#check (AlgebraicGeometry.AlgebraicStack.exists_isAdmissibleBlowup_flat_finitePresentation :
  ∀ {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ Y.toGroupoids)
    [AlgebraicStack.FiniteType f] [AlgebraicStack.QuasiSeparated f]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    [AlgebraicStack.Flat (pullbackSnd f V.ι)]
    [AlgebraicStack.LocallyOfFinitePresentation (pullbackSnd f V.ι)],
    ∃ (Y' : AlgebraicSpace S) (b : Y' ⟶ Y)
      (P : ObjectProperty (pullback f b).total) (hP : Substack.IsClosed (pullback f b) P),
      AlgebraicSpace.IsAdmissibleBlowup V b ∧
        Substack.restrictsTo P hP (pullbackFst (pullbackSnd f b) (V.inverseImage b).ι) ∧
        AlgebraicStack.Flat (Substack.closedInclusion (pullback f b) P hP ≫ pullbackSnd f b) ∧
          AlgebraicStack.FinitePresentation
            (Substack.closedInclusion (pullback f b) P hP ≫ pullbackSnd f b))

end AlgebraicGeometry.AlgebraicStack
