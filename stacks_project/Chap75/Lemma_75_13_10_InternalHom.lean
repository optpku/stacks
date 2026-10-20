/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.InternalHom.Quasicoherent

/-!
# Quasi-coherence of derived internal Hom on algebraic spaces

Derived internal Hom of a pseudo-coherent source into a bounded-below quasi-coherent target,
or of a perfect source into an unbounded quasi-coherent target, remains in `D_QCoh(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.DerivedCategory
open DerivedCategory.TStructure

noncomputable section

universe u

/- Lemma 75.13.10 (1): derived internal Hom from a pseudo-coherent object to a
bounded-below quasi-coherent object has quasi-coherent cohomology. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_pseudoCoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : ModuleDerived X)
      [(DerivedTensor.Right.functor K).IsLeftAdjoint] (L : DerivedQCoh X),
      IsPseudoCoherent X K →
        (t.plus : ObjectProperty (ModuleDerived X)) L.obj →
          derivedQuasiCoherentModuleProperty X
            ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj))

/- Lemma 75.13.10 (2): derived internal Hom from a perfect object to a quasi-coherent
object has quasi-coherent cohomology. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom.derivedQCoh_of_perfect :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (K : ModuleDerived X)
      [(DerivedTensor.Right.functor K).IsLeftAdjoint] (L : DerivedQCoh X),
      ModuleDerived.IsPerfect K →
        derivedQuasiCoherentModuleProperty X
          ((DerivedTensor.Right.functor K).rightAdjoint.obj L.obj))
