/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeHom.Graph
public import stacks_project.Chap99.Lemma_99_12_1_Mor

/-!
# Graph of a relative morphism as a Hilbert point

The graph of a morphism `f : Z_T ⟶ X_T` over `T` is the closed subspace
`Γ_f ⊂ (Z ×_B X)_T`. Under the standing hypotheses this yields a natural
transformation `Mor_B(Z, X) ⟶ Hilb_{Z ×_B X / B}`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver fiber fiberMap)

noncomputable section

universe u

/- Lemma 99.12.1: taking the graph gives a natural transformation. -/
@[stacks 0D1A] #check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.graph :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [Separated x] [FinitePresentation z] [Flat z] [Proper z],
    AlgebraicGeometry.AlgebraicSpace.RelativeHom.mor z x ⟶
      AlgebraicGeometry.AlgebraicSpace.RelativeHom.hilb z x)

/- The finite-presentation specialization of the relative-product Hilbert functor. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeHom.hilbToHilbert :
  ∀ {S : Scheme.{u}} {Z B X : AlgebraicSpace S} (z : Z ⟶ B) (x : X ⟶ B)
    [FinitePresentation (AlgebraicGeometry.AlgebraicSpace.RelativeHom.productHom z x)],
    AlgebraicGeometry.AlgebraicSpace.RelativeHom.hilb z x ⟶
      Hilbert.hilbert (AlgebraicGeometry.AlgebraicSpace.RelativeHom.productHom z x))
