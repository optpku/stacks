/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
public import stacks_project.Chap92.Lemma_92_6_1_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization of the cotangent complex at the bottom

If `A → A' → B` are ring maps with `B = B ⊗[A]^L A'` in `D(A')`, then the
canonical comparison `toRelativeMap : L_{B/A} ⟶ L_{B/A'}` is an isomorphism
in `D(B)`.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open RingedSite.Cotangent.Functoriality

universe u

namespace Algebra.CotangentComplex

/-- The commutative square of ring maps `A → A' → B` with identity on `B`. -/
theorem idCodomainCommSq (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B] :
    CommSq (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (algebraMap A' B)) (𝟙 (CommRingCat.of B)) :=
  sorry

/-- Lemma 92.8.1. Let `A → A' → B` be ring maps such that `B = B ⊗[A]^L A'`.
Then `L_{B/A} = L_{B/A'}` in `D(B)`, as invertibility of
`toRelativeMap A A' B : derived A B ⟶ derived A' B`. -/
@[stacks 08QZ]
theorem toRelativeMap_isIso_of_derivedTensor (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B)) :
    IsIso (toRelativeMap A A' B) :=
  sorry

/-- Under the derived-tensor identity `B = B ⊗[A]^L A'`, the objects
`derived A B` and `derived A' B` are isomorphic in `D(B)`. -/
theorem isIsomorphic_derived_of_derivedTensor (A A' B : Type u)
    [CommRing A] [CommRing A'] [CommRing B]
    [Algebra A A'] [Algebra A' B] [Algebra A B] [IsScalarTower A A' B]
    (h : InducesDerivedTensorQuasiIso (idCodomainCommSq A A' B)) :
    IsIsomorphic (derived A B) (derived A' B) :=
  sorry

end Algebra.CotangentComplex
