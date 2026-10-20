/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalSpectrum.EtaleCompletion
public import stacks_project.Chap87.Lemma_87_19_13_Completion
public import stacks_project.Chap87.Lemma_87_19_13_Over
public import stacks_project.Chap87.Lemma_87_9_10_Map

/-! # Formal spectra of completed étale algebras

Formal spectrum acts on all continuous algebra maps of completions. Raw algebra
homomorphisms still induce their canonical maps of completions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalRing
open AlgebraicGeometry.AffineFormalAlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B : Type u} [CommRing B] [TopologicalSpace B]
  [TopologicalRing.IsWeaklyAdmissibleRing B] (hB : Spec (.of B) ⟶ S)
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfEtaleCompletion hB :
  (CommAlgCat.EtaleCompletion.{u} B)ᵒᵖ ⥤ AffineEtaleOver (spf B hB).obj)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.spfMap_weakIdealCompletion_map hB :
  ∀ {A A' : Type u} [CommRing A] [Algebra B A] [CommRing A'] [Algebra B A']
    (f : A →ₐ[B] A'),
    spf (weakIdealCompletion B A') (specHom_weakIdealCompletion hB A') ⟶
      spf (weakIdealCompletion B A) (specHom_weakIdealCompletion hB A))
