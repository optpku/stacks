/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.DerivedGlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.Module.EnlargedGrothendieck

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.34.5. For an fppf hypercovering augmentation, the canonical comparison
of derived global sections is invertible on every unbounded complex with
quasi-coherent homology, using the total spaces-étale augmentation. -/
@[stacks 0DHG] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaPullbackComparison_app_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X)
      (ha : IsFppfHypercovering a) (K : QCohDerived.Base X),
      IsIso ((AlgebraicGeometry.AlgebraicSpace.Simplicial.rGammaPullbackComparison a ha).app K.obj))
