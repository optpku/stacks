/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flat.Localization.AtPrime.Fiber
public import ReasLib.RingTheory.Flatness.Nilpotent

/-!
# Nilpotent Fiber Flatness

This sibling leaf combines the nilpotent quotient criterion with the independent prime-fiber
localization criterion.  Keeping the composition here avoids a reverse dependency from the
prime-local leaf to the nilpotent flatness owner.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace RingHom.Flat.Nilpotent

variable {R : Type u} {S : Type v} {S' : Type w} {M : Type x}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
variable [AddCommGroup M] [Module S' M]
variable {I : Ideal R}

/-- Lemma 10.101.8 (Critère de platitude par fibres: Nilpotent case) (Stacks `06A5`): quotient
flatness and base flatness imply flatness of `R → S_q` at every prime with nontrivial restricted
fiber. -/
@[stacks 06A5 "nilpotent fiber criterion at a prime"]
theorem atPrime_of_quotient_flat
    (hI : IsNilpotent I)
    (hquot : Module.Flat (S ⧸ Ideal.map (algebraMap R S) I)
      ((RestrictScalars S S' M) ⧸
        (Ideal.map (algebraMap R S) I •
          (⊤ : Submodule S (RestrictScalars S S' M)))))
    (hflat_R : Module.Flat R (RestrictScalars R S' M))
    (q : PrimeSpectrum S)
    (h : Nontrivial ((RestrictScalars S S' M) ⊗[S] q.asIdeal.ResidueField)) :
    (algebraMap R (Localization.AtPrime q.asIdeal)).Flat := sorry

end RingHom.Flat.Nilpotent
