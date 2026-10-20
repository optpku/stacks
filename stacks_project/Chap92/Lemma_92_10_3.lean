/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Frobenius
import StacksCheckRecall

/-!
# Vanishing of the cotangent complex for perfect rings

In characteristic `p`, if `A` and `B` are perfect then the André-Quillen complex
`L_{B/A}` is the zero object of `D(B)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 92.10.3. Let `p` be a prime number. Let `A ⟶ B` be a ring homomorphism and
assume that `p = 0` in `A`. If `A` and `B` are perfect, then `L_{B/A}` is zero in
`D(B)`. -/
@[stacks 0G60] #check (Algebra.CotangentComplex.Frobenius.cotangentComplex_isZero :
  ∀ (p : ℕ) [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hp : (p : A) = 0) [PerfectRing A p] [PerfectRing B p],
    IsZero (DerivedCategory.Q.obj (RingHom.cotangentComplex f)))

#check (Algebra.CotangentComplex.Frobenius.derived_isZero :
  ∀ (p : ℕ) [Fact p.Prime] (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (hp : (p : A) = 0) [PerfectRing A p] [PerfectRing B p],
    IsZero (DerivedCategory.Q.obj (Algebra.cotangentComplex A B)))
