/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Regular.JRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Fields are J-rings

@stack 07PJ
-/

@[expose] public section

universe u v

namespace IsJ0Ring

/-- Every field is `J-0`. -/
@[stacks 07PJ "(1), fields are J-0"]
instance field (K : Type u) [Field K] : IsJ0Ring K where
  __ := (inferInstance : IsNoetherianRing K)
  exists_nonempty_open_subset_regularLocus := by
    refine ⟨Set.univ, isOpen_univ, Set.univ_nonempty, ?_⟩
    intro p hp
    change IsRegularLocalRing (Localization.AtPrime p.asIdeal)
    letI : p.asIdeal.IsPrime := p.isPrime
    letI : IsRegularRing K := inferInstance
    infer_instance

end IsJ0Ring

namespace IsJ1Ring

/-- Every field is `J-1`. -/
@[stacks 07PJ "(1), fields are J-1"]
instance field (K : Type u) [Field K] : IsJ1Ring K where
  __ := (inferInstance : IsNoetherianRing K)
  regularLocus_isOpen := by
    have h : PrimeSpectrum.regularLocus K = Set.univ := by
      apply Set.eq_univ_of_forall
      intro p
      change IsRegularLocalRing (Localization.AtPrime p.asIdeal)
      letI : p.asIdeal.IsPrime := p.isPrime
      letI : IsRegularRing K := inferInstance
      infer_instance
    rw [h]
    exact isOpen_univ

end IsJ1Ring

namespace IsJ2Ring

/-- Every field is `J-2`. -/
@[stacks 07PJ "(1), fields"]
instance field (K : Type u) [Field K] : IsJ2Ring.{u, v} K := sorry

end IsJ2Ring
