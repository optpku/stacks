/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.Nakayama.Basic
import StacksCheckRecall

@[expose] public section

universe u v w

/-!
# Lemma 10.20.1 (Nakayama's lemma)

@stack 00DV

The numbered clauses recall the reusable submodule and quotient-map Nakayama APIs directly.
-/

/-
Layering for this item:
* primary domain: commutative algebra, specifically Nakayama-style statements for submodules,
  quotient maps, and localization away from one element;
* core/canonical owners sampled for this file:
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`,
  `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot`,
  `Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup`,
  `LinearMap.quotientMapByIdeal`;
* source-facing layer: the top/range/span specializations that match the numbered Stacks item;
* bridge/view layer: quotient-map surjectivity and away-localization conclusions.

Primitive data are the ideal, the relevant submodules, and the underlying linear map; the quotient
and localization statements are derived API built from those owner abstractions.
-/

/- Lemma 10.20.1 (Nakayama's lemma) (1): the finite-module annihilator form is the
canonical theorem `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`; the
source specialization with `I • (⊤ : Submodule R M) = ⊤` is obtained by taking the top
submodule. -/
@[stacks 00DV "(1)"]
#check @Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul

/- Lemma 10.20.1 (Nakayama's lemma) (2): the Jacobson-radical zero-module form is owned by
`Module.subsingleton_of_smul_top_eq_top_of_le_jacobson`. -/
@[stacks 00DV "(2)"]
#check @Module.subsingleton_of_smul_top_eq_top_of_le_jacobson

/- Lemma 10.20.1 (Nakayama's lemma) (3): the canonical localized submodule form is owned by
`Submodule.exists_sub_one_mem_and_smul_top_le_of_sup_eq_top`. -/
@[stacks 00DV "(3)"]
#check @Submodule.exists_sub_one_mem_and_smul_top_le_of_sup_eq_top

/- Lemma 10.20.1 (Nakayama's lemma) (4): the Jacobson-radical submodule form is the
canonical theorem `Submodule.eq_top_of_sup_eq_top_of_le_jacobson`. -/
@[stacks 00DV "(4)"]
#check @Submodule.eq_top_of_sup_eq_top_of_le_jacobson

/- Lemma 10.20.1 (Nakayama's lemma) (5): localized surjectivity from a quotient map is owned by
`LinearMap.exists_localizedAway_surjective`. -/
@[stacks 00DV "(5)"]
#check (LinearMap.exists_localizedAway_surjective :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f : N →ₗ[R] M) (I : Ideal R)
    [Module.Finite R M], Function.Surjective (f.quotientMapByIdeal I) →
    ∃ r : R, r - 1 ∈ I ∧ Function.Surjective (LocalizedModule.map (Submonoid.powers r) f))

/- Lemma 10.20.1 (Nakayama's lemma) (6): surjectivity from a quotient map over a
Jacobson-radical ideal is owned by `LinearMap.surjective_of_quotientMapByIdeal_surjective_of_le_jacobson`.
-/
@[stacks 00DV "(6)"]
#check @LinearMap.surjective_of_quotientMapByIdeal_surjective_of_le_jacobson

/- Lemma 10.20.1 (Nakayama's lemma) (7): a finite family is represented by its underlying set;
the reusable owner gives the same localized-span conclusion for any set. -/
@[stacks 00DV "(7)"]
#check @Submodule.exists_sub_one_mem_and_localized_eq_top_of_quotient_span_eq_top

/- Lemma 10.20.1 (Nakayama's lemma) (8): finite-set generation modulo a
Jacobson-radical ideal is owned by `Submodule.span_eq_top_of_quotient_span_eq_top_of_le_jacobson`.
-/
@[stacks 00DV "(8)"]
#check @Submodule.span_eq_top_of_quotient_span_eq_top_of_le_jacobson

/- Lemma 10.20.1 (Nakayama's lemma) (9): the nilpotent zero-module form is owned by
`Module.subsingleton_of_smul_top_eq_top_of_isNilpotent`. -/
@[stacks 00DV "(9)"]
#check @Module.subsingleton_of_smul_top_eq_top_of_isNilpotent

/- Lemma 10.20.1 (Nakayama's lemma) (10): the nilpotent submodule form is owned by
`Submodule.eq_top_of_sup_eq_top_of_isNilpotent`. -/
@[stacks 00DV "(10)"]
#check @Submodule.eq_top_of_sup_eq_top_of_isNilpotent

/- Lemma 10.20.1 (Nakayama's lemma) (11): the nilpotent quotient-map form is owned by
`LinearMap.surjective_of_quotientMapByIdeal_surjective_of_isNilpotent`. -/
@[stacks 00DV "(11)"]
#check @LinearMap.surjective_of_quotientMapByIdeal_surjective_of_isNilpotent

/- Lemma 10.20.1 (Nakayama's lemma) (12): nilpotent quotient-span generation is owned by
`Submodule.span_eq_top_of_quotient_span_eq_top_of_isNilpotent`. -/
@[stacks 00DV "(12)"]
#check @Submodule.span_eq_top_of_quotient_span_eq_top_of_isNilpotent
