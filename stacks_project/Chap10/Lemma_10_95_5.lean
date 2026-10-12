/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.CountablyGenerated.BaseChange.DirectSum
import StacksCheckRecall

/-!
# Countably generated submodules and direct sums after base change

@stack 05A8
-/

@[expose] public section

universe u v w x

open scoped TensorProduct

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {I : Type x}

/- Lemma 10.95.5 (05A8): for an internal direct-sum decomposition of `S ⊗[R] M` into
countably generated submodules, every countably generated submodule of `M` has a countably
generated enlargement whose scalar extension is a sum of a subfamily. -/
@[stacks 05A8]
#check (Submodule.CountablyGenerated.BaseChange.exists_supermodule_eq_iSup
  (R := R) (S := S) (M := M) (I := I) :
    ∀ (Q : I → Submodule S (S ⊗[R] M)), iSupIndep Q → (⨆ i, Q i) = ⊤ →
      (∀ i, (Q i).CountablyGenerated) → ∀ {N : Submodule R M},
        N.CountablyGenerated →
          ∃ (N' : Submodule R M) (J : Set I),
            N ≤ N' ∧ N'.CountablyGenerated ∧
              N'.baseChange S = ⨆ i : J, Q i.1)

end

#check @DirectSum.Decomposition.exists_countable_subfamily_le
#check @DirectSum.IsInternal.exists_countable_subfamily_le
#check @Submodule.CountablyGenerated.BaseChange.exists_supermodule_eq_iSup_of_decomposition
#check @Submodule.CountablyGenerated.BaseChange.exists_supermodule_eq_iSup_of_isInternal
#check @Submodule.CountablyGenerated.BaseChange.exists_supermodule_eq_iSup
