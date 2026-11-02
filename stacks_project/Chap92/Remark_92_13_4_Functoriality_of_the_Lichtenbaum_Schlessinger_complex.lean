/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Presentation.LichtenbaumSchlessinger.Functoriality
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

open CategoryTheory
open HomologicalComplex
open Algebra.Presentation
open scoped TensorProduct ChangeOfRings

universe u

/-!
# Functoriality of the Lichtenbaum–Schlessinger complex

A commutative square of ring maps, together with compatible polynomial
presentations whose relation indices extend along a coproduct, induces a
canonical cochain map of Lichtenbaum–Schlessinger complexes. Tracing the
choices of Lemma 92.13.3, this comparison commutes with cotangent-complex
functoriality in the derived category.
-/

@[expose] public section

/-!
Remark 92.13.4 (Functoriality of the Lichtenbaum-Schlessinger complex)
-/
@[stacks 09D7]
#check ((fun {A B A' B' ι ι' σ τ : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B']
    (P : Algebra.Presentation A B ι σ)
    (P' : Algebra.Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) =>
    Algebra.Presentation.LichtenbaumSchlessinger.map P P' f Sum.inl h_rel) :
  ∀ {A B A' B' ι ι' σ τ : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B']
    (P : Algebra.Presentation A B ι σ)
    (P' : Algebra.Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)),
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (Algebra.Presentation.LichtenbaumSchlessinger.complex P) ⟶
      Algebra.Presentation.LichtenbaumSchlessinger.complex P')

/-! Remark 92.13.4 (Functoriality of the Lichtenbaum-Schlessinger complex) -/
@[stacks 09D7]
#check ((fun {A B A' B' ι ι' σ τ : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B']
    (P : Algebra.Presentation A B ι σ)
    (P' : Algebra.Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) =>
    Algebra.Presentation.LichtenbaumSchlessinger.comparison_commSq P P' f Sum.inl h_rel) :
  ∀ {A B A' B' ι ι' σ τ : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
    [IsScalarTower A A' B'] [IsScalarTower A B B']
    (P : Algebra.Presentation A B ι σ)
    (P' : Algebra.Presentation A' B' ι' (σ ⊕ τ))
    (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)),
    CommSq
      (DerivedCategory.Q.map
        (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (Algebra.Presentation.LichtenbaumSchlessinger.toComplex P)))
      (DerivedCategory.Q.map
        (Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
          (algebraMap A A') (algebraMap B B')
            (Algebra.Presentation.LichtenbaumSchlessinger.algebraMap_comp)))
      (DerivedCategory.Q.map
        (Algebra.Presentation.LichtenbaumSchlessinger.map P P' f Sum.inl h_rel))
      (DerivedCategory.Q.map
        (Algebra.Presentation.LichtenbaumSchlessinger.toComplex P')))
