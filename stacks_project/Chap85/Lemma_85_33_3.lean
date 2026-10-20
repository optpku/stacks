/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfCohomologicalDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.DegreeZeroDerived
import StacksCheckRecall

/-! # Étale cohomological descent for fppf hypercoverings -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open scoped Simplicial

/- Lemma 85.33.3: For an fppf hypercovering of an algebraic space, the canonical
unit of the total étale augmentation is invertible on bounded-below complexes
of abelian étale sheaves. -/
@[stacks 0DH7] #check
  (AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived.plusDerivedUnit_app_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      {U : SimplicialObject (AlgebraicSpace S)}
      (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a)
      (K : DerivedCategory.Plus (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})),
      IsIso ((EtaleDerived.plusDerivedUnit a).app K))

#check (AlgebraicGeometry.AlgebraicSpace.Simplicial.EtaleDerived.plusDerivedUnit_isIso :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (ha : IsFppfHypercovering a),
    IsIso (EtaleDerived.plusDerivedUnit a))
