/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.Completion.Flat
public import ReasLib.RingTheory.Completion.FormallyUnramified
public import ReasLib.RingTheory.Completion.NonExcellent

universe u

open IsLocalRing

variable {A : Type u} [CommRing A]
variable {p : ℕ} [Fact p.Prime] [CharP A p]

section

variable [IsNoetherianRing A] [IsLocalRing A] [CharP (ResidueField A) p]
variable [FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
  (ResidueField A)]

/- Lemma 110.44.2 (1): the canonical map from a Noetherian local ring of prime
characteristic `p` with `[κ : κ ^ p] < ∞` to its completion is flat. -/
@[stacks 0G66] #check
  (adicCompletion_algebraMap_flat (maximalIdeal A) :
    (algebraMap A (AdicCompletion (maximalIdeal A) A)).Flat)

/- Lemma 110.44.2 (2): the same completion map is formally unramified. -/
@[stacks 0G66] #check (AdicCompletion.instFormallyUnramified :
  Algebra.FormallyUnramified A (AdicCompletion (maximalIdeal A) A))

end

section

variable [IsRegularLocalRing A] [CharP (ResidueField A) p]
variable [FiniteDimensional (FieldExtension.Frobenius.subfield p (ResidueField A))
  (ResidueField A)]

/- Lemma 110.44.2 (3): for a regular non-excellent ring, the completion map is
not formally étale. -/
@[stacks 0G66] #check (AdicCompletion.algebraMap_not_formallyEtale_of_not_isExcellentRing :
  (¬ IsExcellentRing.{u, u} A) →
    ¬ Algebra.FormallyEtale A (AdicCompletion (maximalIdeal A) A))

end
