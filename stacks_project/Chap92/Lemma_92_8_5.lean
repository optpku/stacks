/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of the relative cotangent complex on top

If `L_{C/B}` vanishes in `D(C)`, the first transitivity map
`tensorMap : tensor A B C ⟶ derived A C` is an isomorphism.
-/

@[expose] public section

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.8.5: let `A → B → C` be ring maps such that `L_{C/B} = 0`. Then
`L_{C/A} = L_{B/A} ⊗^L_B C` in `D(C)`, as invertibility of
`tensorMap A B C : tensor A B C ⟶ derived A C`. -/
@[stacks 08R3]
theorem tensorMap_isIso_of_isZero (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    (h_zero : IsZero (derived B C)) : IsIso (tensorMap A B C) :=
  sorry

/-- The first transitivity map `tensorMap A B C` is an isomorphism if and only if
`derived B C` vanishes. -/
theorem isIso_tensorMap_iff_isZero_derived (A B C : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    IsIso (tensorMap A B C) ↔ IsZero (derived B C) :=
  sorry

end Algebra.CotangentComplex
