/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.RingHom.ULift
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski
public import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobi-Zariski sequences for filtered colimits

The filtered-colimit predicate is the categorical `MorphismProperty.ind` owner
specialized to local complete-intersection ring maps. The resulting
Jacobi-Zariski sequence remains exact on the left.

@stack 07D5
-/

@[expose] public section

open Algebra
open CategoryTheory MorphismProperty

universe u v

noncomputable section

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring map is a filtered colimit of local complete-intersection maps when its common-universe
lift satisfies the canonical categorical `MorphismProperty.ind` predicate. -/
@[stacks 07D5 "filtered colimits of local complete-intersection maps"]
abbrev IsFilteredColimitOfLocalCompleteIntersection (f : R →+* S) : Prop :=
  -- Local instance justification (defeq pin): expose the algebra map represented by `f`.
  let _ : Algebra R S := f.toAlgebra
  -- Local instance justification (defeq pin): fix the codomain lift used by `ind`.
  let _ : Algebra R (ULift S) := ULift.algebra
  -- Local instance justification (defeq pin): identify the common-universe lifted structure map.
  let _ : Algebra (ULift.{v} R) (ULift S) := ULift.algebra' R (ULift S)
  ind.{max u v, max u v, max u v + 1} (toMorphismProperty IsLocalCompleteIntersection)
    (CommRingCat.ofHom (algebraMap (ULift.{v} R) (ULift S)))

end RingHom

section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v}

/-- The left-edge injectivity and middle exactness supplied by a filtered-colimit
local-complete-intersection hypothesis. -/
theorem presentation_jacobi_zariski_exact_sequence_with_zero_left_of_isFilteredColimitOfLocalCompleteIntersection
    (P : Generators A B ι)
    (hC : (algebraMap B C).IsFilteredColimitOfLocalCompleteIntersection) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := sorry

/-- Lemma 15.33.7 (1), tag `07D5`: filtered colimits of
local complete-intersection maps preserve injectivity of the left Jacobi-Zariski map. -/
@[stacks 07D5 "(1)"]
theorem presentationJacobiZariskiLeftSequence_injective_f_of_filteredColimitOfLci
    (P : Generators A B ι)
    (hC : (algebraMap B C).IsFilteredColimitOfLocalCompleteIntersection) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) := sorry

/-- Lemma 15.33.7 (2), tag `07D5`: filtered colimits of
local complete-intersection maps preserve exactness of the left Jacobi-Zariski row. -/
@[stacks 07D5 "(2)"]
theorem presentationJacobiZariskiLeftSequence_exact_of_filteredColimitOfLci
    (P : Generators A B ι)
    (hC : (algebraMap B C).IsFilteredColimitOfLocalCompleteIntersection) :
    (presentationJacobiZariskiLeftSequence C P).Exact := sorry

end
