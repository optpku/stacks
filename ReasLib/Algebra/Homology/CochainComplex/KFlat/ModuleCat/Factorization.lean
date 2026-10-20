/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Resolution
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through K-flat complexes

@stack 0G6M

A morphism whose source is K-flat factors up to homotopy through a quasi-isomorphism from a
K-flat complex.  If the source is also termwise flat, the intermediate complex can be chosen
termwise flat as well.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat R) ℤ}

/-- Lemma 15.59.16 (1), in the commutative-ring setting: a morphism with K-flat source factors
up to homotopy through a quasi-isomorphism whose source is K-flat. -/
@[stacks 0G6M "K-flat factorization"]
theorem exists_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

/-- Lemma 15.59.16 (2), in the commutative-ring setting: when the K-flat source is termwise
flat, the intermediate complex in the factorization can also be chosen termwise flat. -/
@[stacks 0G6M "termwise-flat K-flat factorization"]
theorem exists_termwiseFlat_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) (hFlat : K.IsTermwiseFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ N.IsTermwiseFlat ∧ QuasiIso c := sorry

end CochainComplex
