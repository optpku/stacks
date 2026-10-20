/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.Projective.Dimension.WellOrderedUnion
import StacksCheckRecall

/-!
# Projective Dimension of Well-Ordered Unions

@stack 0D1U
-/

@[expose] public section

universe u v w

open CategoryTheory

variable {R : Type u} [Ring R]
variable {ι : Type w} [LinearOrder ι] [IsWellOrder ι (· < ·)]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable (M_ : ι → Submodule R M) (hmono : Monotone M_) (hcover : iSup M_ = ⊤) (n : ℕ)

/- Lemma 10.109.11 (Stacks `0D1U`): if the increasing, well-ordered family `M_` covers `M` and
every quotient of `M_ e` by the supremum of its strictly earlier stages has projective dimension
at most `n`, then `M` has projective dimension at most `n`. The deterministic lower-stage
quotient is the canonical `Submodule.successiveQuotient M_ e`. -/
@[stacks 0D1U]
#check (HasProjectiveDimensionLE.of_wellOrdered_union M_ hmono hcover n :
  (∀ e : ι,
    HasProjectiveDimensionLE
      (ModuleCat.of R (Submodule.successiveQuotient M_ e)) n) →
    HasProjectiveDimensionLE (ModuleCat.of R M) n)

@[stacks 0D1U "well-ordered union owner"]
#check @HasProjectiveDimensionLE.of_wellOrdered_union
