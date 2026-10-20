/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
import StacksCheckRecall

/-!
# Vanishing of the relative cotangent complex on top

If `L_{C/B}` vanishes in `D(C)`, the first transitivity map
`tensorMap : tensor A B C ⟶ derived A C` is an isomorphism.
-/

@[expose] public section

universe u

/- Lemma 92.8.5: let `A → B → C` be ring maps such that `L_{C/B} = 0`. Then
`L_{C/A} = L_{B/A} ⊗^L_B C` in `D(C)`, as invertibility of the first
canonical transitivity map. -/
@[stacks 08R3] #check (Algebra.CotangentComplex.tensorMap_isIso_of_isZero :
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    CategoryTheory.Limits.IsZero (Algebra.CotangentComplex.derived B C) →
      CategoryTheory.IsIso (Algebra.CotangentComplex.tensorMap A B C))

#check (Algebra.CotangentComplex.isIso_tensorMap_iff_isZero_derived :
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    CategoryTheory.IsIso (Algebra.CotangentComplex.tensorMap A B C) ↔
      CategoryTheory.Limits.IsZero (Algebra.CotangentComplex.derived B C))
