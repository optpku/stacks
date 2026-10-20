/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.Derived
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Rig-étaleness and the derived completed naive cotangent complex

Rig-étaleness over a Noetherian pair is characterized by annihilation of
the completed naive cotangent object in the derived category.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.RigEtale

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- A topologically finite type algebra over a Noetherian pair is rig-étale
if and only if some power of the ideal acts by zero on the completed naive
cotangent object of a finite completed presentation in the derived category. -/
theorem iff_exists_pow_smul_id (I : Ideal A) (B : Type u)
    [CommRing B] [Algebra A B] [TopologicallyFiniteType I B] :
    RigEtale I B ↔
      ∃ (c : ℕ) (ι : Type u) (_ : Fintype ι)
          (P : NaiveCotangent.Adic.Presentation A B I ι),
        ∀ a ∈ I ^ c,
          (algebraMap A B a) • 𝟙 (NaiveCotangent.Adic.naiveCotangentObject I P) = 0 :=
  sorry

end Algebra.RigEtale
