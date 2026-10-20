/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.RigEtale.Derived

/-!
# Rig-étale algebras over a Noetherian pair

An object `B` of (88.2.0.2) is rig-étale over `(A, I)` when some power of `I`
acts by zero on the completed naive cotangent complex `NL_{B/A}^∧` in `D(B)`.
-/

@[expose] public section

open CategoryTheory

universe u

/- Definition 88.8.1: Let `A` be a Noetherian ring and let `I ⊂ A` be an ideal.
Let `B` be an object of (88.2.0.2). We say `B` is rig-étale over `(A, I)` if
there exists an integer `c ≥ 0` such that for all `a ∈ I ^ c` multiplication
by `a` on `NL_{B/A}^∧` is zero in `D(B)`. -/
@[stacks 0GAY] #check (Algebra.RigEtale.iff_exists_pow_smul_id :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B] [Algebra.TopologicallyFiniteType I B],
    Algebra.RigEtale I B ↔
      ∃ (c : ℕ) (ι : Type u) (_ : Fintype ι)
          (P : Algebra.NaiveCotangent.Adic.Presentation A B I ι),
        ∀ a ∈ I ^ c,
          (algebraMap A B a) • 𝟙 (Algebra.NaiveCotangent.Adic.naiveCotangentObject I P) = 0)
