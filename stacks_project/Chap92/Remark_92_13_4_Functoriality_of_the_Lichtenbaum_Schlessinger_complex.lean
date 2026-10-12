/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Remark_92_13_4_Functoriality_of_the_Lichtenbaum_Schlessinger_complex_Comparison
public import stacks_project.Chap92.Remark_92_13_4_Functoriality_of_the_Lichtenbaum_Schlessinger_complex_Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of the Lichtenbaum–Schlessinger complex

A commutative square of ring maps, together with compatible polynomial
presentations whose relation indices extend along a coproduct, induces a
canonical cochain map of Lichtenbaum–Schlessinger complexes. Tracing the
choices of Lemma 92.13.3, this comparison commutes with cotangent-complex
functoriality.
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open Algebra.Presentation
open Algebra.Presentation.LichtenbaumSchlessinger

noncomputable section

universe u

namespace Algebra.Presentation.LichtenbaumSchlessinger

variable {A B A' B' ι ι' σ τ : Type u}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra A B] [Algebra A' B'] [Algebra A A'] [Algebra B B'] [Algebra A B']
variable [IsScalarTower A A' B'] [IsScalarTower A B B']

/-- Remark 92.13.4 (Functoriality of the Lichtenbaum-Schlessinger complex) (1)
A commutative square of ring maps together with a factorization of polynomial
presentations `P` of `B` over `A` and `P'` of `B'` over `A'`, with relation
indices `T' = T ⨿ S` realized as `σ ⊕ τ` and with
`f.toRingHom (P.relation t) = P'.relation (Sum.inl t)`, induces a canonical
cochain map of Lichtenbaum–Schlessinger complexes
`extendScalars (algebraMap B B') ▸ complex P ⟶ complex P'`. -/
@[stacks 09D7]
abbrev functorialityMap (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complex P) ⟶
      complex P' :=
  map P P' f h_rel

/-- Unfolding of the source-facing cochain map recovers `map`. -/
theorem functorialityMap_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    functorialityMap P P' f h_rel = map P P' f h_rel := sorry

/-- Remark 92.13.4 (Functoriality of the Lichtenbaum-Schlessinger complex) (2)
Tracing the choices of Lemma 92.13.3, the comparison maps
`toComplex P : L_{B/A} ⟶ complex P` and `toComplex P' : L_{B'/A'} ⟶ complex P'`
fit in a commutative square with `map` and with
`Algebra.CotangentComplex.map` of the underlying ring-homomorphism square. -/
@[stacks 09D7]
abbrev functoriality_commSq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    CommSq
      (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (toComplex P))
      (Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
        (algebraMap A A') (algebraMap B B') algebraMap_comp)
      (map P P' f h_rel) (toComplex P') :=
  comparison_commSq P P' f h_rel

/-- Unfolding of the source-facing comparison square recovers `comparison_commSq`. -/
theorem functoriality_commSq_eq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    functoriality_commSq P P' f h_rel = comparison_commSq P P' f h_rel := sorry

end Algebra.Presentation.LichtenbaumSchlessinger
