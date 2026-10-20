module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap92.Lemma_92_13_3_Comparison
public import stacks_project.Chap92.Lemma_92_3_4_DirectLimit
public import stacks_project.Chap92.Remark_92_13_4_Functoriality_of_the_Lichtenbaum_Schlessinger_complex_Map

/-!
# Compatibility of Lichtenbaum–Schlessinger functoriality with `toComplex`

The cochain map of Lichtenbaum–Schlessinger complexes induced by a commutative
square of algebras commutes with the comparison maps `toComplex` of Lemma 92.13.3
and with `Algebra.CotangentComplex.map`.
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

/-- The two paths around a commutative square of algebra maps agree. -/
theorem algebraMap_comp :
    (algebraMap A' B').comp (algebraMap A A') =
      (algebraMap B B').comp (algebraMap A B) := sorry

/-- The comparison maps `toComplex` of Lemma 92.13.3 fit in a commutative square
with Lichtenbaum–Schlessinger functoriality and cotangent-complex functoriality. -/
theorem comparison_commSq (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    CommSq
      (((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (toComplex P))
      (Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
        (algebraMap A A') (algebraMap B B') algebraMap_comp)
      (map P P' f h_rel) (toComplex P') := sorry

/-- Unfolding of the comparison square recovers the four cochain maps of the
source diagram. -/
theorem comparison_commSq_w (P : Presentation A B ι σ)
    (P' : Presentation A' B' ι' (σ ⊕ τ)) (f : P.toExtension.Hom P'.toExtension)
    (h_rel : ∀ t, f.toRingHom (P.relation t) = P'.relation (Sum.inl t)) :
    ((ModuleCat.extendScalars (algebraMap B B')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (toComplex P) ≫
        map P P' f h_rel =
      Algebra.CotangentComplex.map (algebraMap A B) (algebraMap A' B')
          (algebraMap A A') (algebraMap B B') algebraMap_comp ≫
        toComplex P' := sorry

end Algebra.Presentation.LichtenbaumSchlessinger
