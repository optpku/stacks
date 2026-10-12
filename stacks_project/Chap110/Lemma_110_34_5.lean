/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.LocallyFree.ProjectiveNotLocallyFree
import StacksCheckRecall

@[expose] public section

universe u v

namespace Module

/- Lemma 110.34.5: there exists a countable ring `R` and a projective `R`-module `M`
which is an internal direct sum of countably many finite locally free rank-1 modules,
yet `M` is not locally free. -/
@[stacks 05WL]
#check (Module.exists_countable_projective_directSum_rankOne_not_locallyFree :
    ∃ (R : Type u) (_ : CommRing R) (_ : Countable R) (M : Type v)
      (_ : AddCommGroup M) (_ : Module R M) (L : ℕ → Submodule R M),
      Projective R M ∧ iSupIndep L ∧ iSup L = ⊤ ∧
        (∀ n, FiniteLocallyFreeOfRank R (L n) 1) ∧ ¬ LocallyFree R M)

end Module
