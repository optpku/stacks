module

public import stacks_project.Chap64.Lemma_64_15_6_MkAddEquiv
public import stacks_project.Chap64.Lemma_64_20_6_ZModPow
public import stacks_project.Chap64.Proposition_64_10_2_Trace

/-!
# Stage traces of perfect derived endomorphisms over Z/ℓ^{n+1}

The traces `t_n = Tr(π_n | K_n)` of a family of perfect derived endomorphisms,
identified with elements of `ZMod (ℓ ^ (n + 1))` via the commutator quotient
of a commutative ring.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open scoped Ring

namespace DerivedCategory.IsPerfect

variable {ℓ : ℕ}
variable (K : (n : ℕ) → DerivedCategory (ModuleCat.{u} (ZMod (ℓ ^ (n + 1)))))
variable (hK : ∀ n, (K n).IsPerfect)
variable (π : ∀ n, End (K n))

/-- The stage trace `t_n = Tr(π_n | K_n)` in `ZMod (ℓ ^ (n + 1))`, obtained by
transporting `traceNatural` along `mkAddEquiv`. -/
noncomputable def stageTrace (n : ℕ) : ZMod (ℓ ^ (n + 1)) :=
  Ring.CommutatorQuotient.mkAddEquiv.symm ((hK n).traceNatural (π n))

/-- The stage trace is the inverse image of `traceNatural` under `mkAddEquiv`. -/
theorem stageTrace_spec (n : ℕ) :
    Ring.CommutatorQuotient.mk (stageTrace K hK π n) = (hK n).traceNatural (π n) := sorry

/-- Unfolding of `stageTrace` as `mkAddEquiv.symm` of `traceNatural`. -/
theorem stageTrace_eq (n : ℕ) :
    stageTrace K hK π n =
      Ring.CommutatorQuotient.mkAddEquiv.symm ((hK n).traceNatural (π n)) := sorry

end DerivedCategory.IsPerfect
