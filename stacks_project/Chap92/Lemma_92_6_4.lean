/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Product
import StacksCheckRecall

/-!
# Product of cotangent complexes

The comparison `L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` is an isomorphism in `D(B × C)`.
-/

@[expose] public section

universe u

/- Lemma 92.6.4. Let `A → B` and `A → C` be ring maps. Then the map
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` is an isomorphism in `D(B × C)`. -/
@[stacks 08SC] #check (Algebra.CotangentComplex.prodMap_isIso :
  ∀ {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C),
    CategoryTheory.IsIso (Algebra.CotangentComplex.prodMap f g))
