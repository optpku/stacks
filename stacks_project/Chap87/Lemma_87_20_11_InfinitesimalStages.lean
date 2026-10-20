/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap87.Lemma_87_34_3_Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.InfinitesimalStages

/-!
# Reduction and infinitesimal-stage compatibility

The legacy reduction accessors remain available to source consumers. The
canonical stage system takes explicit reduction data in its mathematical owner.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.FormalAlgebraicSpace

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.Reduction.toReductionData :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X],
    Reduction X → ReductionData X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.reduction :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X], AlgebraicSpace S)

#check (AlgebraicGeometry.FormalAlgebraicSpace.reductionι :
  ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X],
    (reduction X).functorOfPoints ⟶ X)

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.factorsThroughStage :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X],
    ReductionData X → ℕ → {U : Over S} → (yoneda.obj U ⟶ X) → Prop)

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.stageFunctor :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X],
    ReductionData X → ℕ → ((Over S)ᵒᵖ ⥤ Type u))

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.infinitesimalStages :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X],
    ReductionData X → (ℕ ⥤ AlgebraicSpace S))

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.infinitesimalCocone :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X),
    Cocone (R.infinitesimalStages ⋙ AlgebraicSpace.forgetToPresheaf))

#check (AlgebraicGeometry.FormalAlgebraicSpace.ReductionData.infinitesimalStageIsoNeighbourhood :
  ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X)
    {n m : ℕ}, n ≤ m → (R.infinitesimalStage n ≅ R.neighbourhoodSpace m n))
