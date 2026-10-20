/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
import StacksCheckRecall

/-!
# Ext annihilation for two-term complexes

This file is the source-facing recall for Lemma 15.85.5.

@stack 0G9F
-/

@[expose] public section

open CategoryTheory

universe u

@[stacks 0G9F "Lemma 15.85.5, equivalence (1)-(3)"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0) =>
  (two_term_ext1_annihilated_tfae K I hKGE hKLE :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I])

@[stacks 0G9F "Lemma 15.85.5, Noetherian equivalence (1)-(5)"]
#check fun {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : DerivedCategory (ModuleCat R)) (I : Ideal R)
    (hKGE : K.IsGE (-1)) (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) (-1)).obj K))
    (hH0 : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj K)) =>
  (two_term_ext1_annihilated_tfae_of_isNoetherianRing
      K I hKGE hKLE hHneg1 hH0 :
    List.TFAE [
      twoTermExtOneAnnihilatedByIdeal K I,
      admits_two_term_free_representative_with_ideal_factorization K I,
      all_two_term_projective_representatives_have_ideal_factorization K I,
      twoTermExtOneAnnihilatedByIdealOnFiniteModules K I,
      admits_two_term_finite_free_representative_with_ideal_factorization K I])

@[stacks 0G9F "Ext-one annihilation condition"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R) =>
  (twoTermExtOneAnnihilatedByIdeal K I : Prop)

@[stacks 0G9F "free representative factorization condition"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R) =>
  (admits_two_term_free_representative_with_ideal_factorization K I : Prop)

@[stacks 0G9F "projective representative factorization condition"]
#check fun {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat R)) (I : Ideal R) =>
  (all_two_term_projective_representatives_have_ideal_factorization K I : Prop)
