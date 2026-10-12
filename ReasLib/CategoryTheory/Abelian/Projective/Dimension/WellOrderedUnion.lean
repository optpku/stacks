/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.Submodule.SuccessiveQuotient

/-!
# Projective dimension and well-ordered submodule unions

This leaf owns the module-theoretic union principle.  The filtration is represented directly by
an increasing family of submodules; ordinal reindexing and free-cover choices belong to a proof,
not to the public interface.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace HasProjectiveDimensionLE

variable {R : Type u} [Ring R]
variable {ι : Type w} [LinearOrder ι] [IsWellOrder ι (· < ·)]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Lemma 10.109.11 (Stacks `0D1U`): a well-ordered increasing union of submodules has
projective dimension at most `n` when every successive quotient has that bound. -/
@[stacks 0D1U]
theorem of_wellOrdered_union
    (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤) (n : ℕ)
    (hquot :
      ∀ e : ι,
        HasProjectiveDimensionLE
          (ModuleCat.of R (Submodule.successiveQuotient M_ e)) n) :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := sorry

end HasProjectiveDimensionLE
