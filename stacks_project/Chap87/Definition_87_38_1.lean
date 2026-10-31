/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 87.38.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `Z ⊂ X` be a closed subspace and denote `Z_n ⊂ X` the `n`th order infinitesimal
neighbourhood `Hom.InfinitesimalNeighbourhood.space i n`. The formal algebraic space
`Completion.subfunctor i`, the fppf-sheafified union of the stages `Z_n`, is
called the completion of `X` along `Z`. -/
@[stacks 0GXU] #check (AlgebraicGeometry.AlgebraicSpace.Completion.subfunctor :
  ∀ {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u} (i : Z ⟶ X), Subfunctor X)

@[stacks 0GXU] #check (AlgebraicGeometry.AlgebraicSpace.Completion.stage :
  ∀ {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u} (i : Z ⟶ X) (n : ℕ), Subfunctor X)

@[stacks 0GXU] #check (AlgebraicGeometry.AlgebraicSpace.Completion.fromStage :
  ∀ {S : Scheme.{u}} {X Z : (Over S)ᵒᵖ ⥤ Type u} (i : Z ⟶ X) (n : ℕ),
    (AlgebraicGeometry.AlgebraicSpace.Completion.stage i n).toFunctor ⟶
      (AlgebraicGeometry.AlgebraicSpace.Completion.subfunctor i).toFunctor)

open AlgebraicGeometry.AlgebraicSpace CategoryTheory.Limits

@[stacks 0GXU] #check (fromNamedStage :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] (n : ℕ),
    (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶
      (Completion.subfunctor (i : Z.functorOfPoints ⟶ X.functorOfPoints)).toFunctor)

@[stacks 0GXU] #check (fromNamedStageCocone :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    Cocone (neighbourhoodSystem i))

@[stacks 0GXU] #check (existsUnique_desc_genericCompletion :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    {F : (Over S)ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
    ∀ (f : (n : ℕ) → (Hom.InfinitesimalNeighbourhood.space i n).functorOfPoints ⟶ F),
    (∀ {n m : ℕ} (h : n ≤ m),
      NatTrans.vcomp (Hom.InfinitesimalNeighbourhood.transition i h) (f m) = f n) →
    ∃! g : (Completion.subfunctor (i : Z.functorOfPoints ⟶ X.functorOfPoints)).toFunctor ⟶ F,
      ∀ n, fromNamedStage i n ≫ g = f n)

#check (completionAlongSubspaceIsoGeneric :
  ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
    completionAlongSubspace i ≅
      (Completion.subfunctor (i : Z.functorOfPoints ⟶ X.functorOfPoints)).toFunctor)
