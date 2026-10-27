/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Coherent.Groupoid
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory

universe u

/- Lemma 103.17.8: In the situation discussed above, the equivalence
QCoh(𝒪_X) ≅ QCoh(U, R, s, t, c) sends coherent sheaves to coherent sheaves and
vice versa, i.e., induces an equivalence Coh(𝒪_X) ≅ Coh(U, R, s, t, c). -/
@[stacks 0GRC]
#check (AlgebraicGeometry.AlgebraicStack.Coh.groupoidEquivalence :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.IsLocallyNoetherian X] (U : AlgebraicSpace S)
    (f : U.toGroupoids ⟶ X) [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f],
    AlgebraicStack.Coh X ≌
      GroupoidAlgebraicSpace.Coh
        (groupoid f (IsRepresentableByAlgebraicSpace.of_toGroupoids U)))
