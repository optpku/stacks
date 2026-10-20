/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.Generators
import StacksCheckRecall

@[expose] public section

universe u

section

variable {A : Type u} [CommSemiring A] {I : Ideal A}
variable {gamma : ℕ → A → A} {S : Set A}
variable (hgamma : DividedPowers.AxiomsOnGenerators I gamma S)

/- Lemma 23.2.4 (07GP): generator-level divided-power identities assemble the canonical divided
power structure with the prescribed operations. -/
@[stacks 07GP]
#check (DividedPowers.AxiomsOnGenerators.existsUnique_dividedPowers hgamma :
  ∃! hI : DividedPowers I,
    ∀ {n : ℕ} {x : A}, x ∈ I → hI.dpow n x = gamma n x)

end

#check @DividedPowers.AxiomsOnGenerators
#check @DividedPowers.AxiomsOnGenerators.dividedPowers_dpow
#check @DividedPowers.AxiomsOnGenerators.eq_dividedPowers_of_dpow_eq
#check @DividedPowers.AxiomsOnGenerators.exists_dividedPowers
#check @DividedPowers.AxiomsOnGenerators.existsUnique_dividedPowers
