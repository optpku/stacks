module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Cardinality

/-!
# Large algebraically closed field extensions

This file constructs algebraically closed extensions whose cardinality exceeds prescribed
cardinal bounds.
-/

@[expose] public section

universe u

namespace Field

/-- Every field admits an algebraically closed extension whose cardinality strictly exceeds two
prescribed cardinal bounds. -/
theorem exists_algClosed_extension_cardinal_gt
    (k : Type u) [Field k] (κ₁ κ₂ : Cardinal.{u}) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : IsAlgClosed K),
      κ₁ < Cardinal.mk K ∧ κ₂ < Cardinal.mk K := by
  classical
  let bound : Cardinal.{u} := Cardinal.mk k ⊔ κ₁ ⊔ κ₂ ⊔ Cardinal.aleph0
  let σ : Type u := Set bound.ord.ToType
  have hbound_le_κ₁ : κ₁ ≤ bound := by
    dsimp [bound]
    exact le_sup_of_le_left <| le_sup_of_le_left <| le_sup_of_le_right le_rfl
  have hbound_le_κ₂ : κ₂ ≤ bound := by
    dsimp [bound]
    exact le_sup_of_le_left <| le_sup_of_le_right le_rfl
  have hbound_le_aleph0 : Cardinal.aleph0 ≤ bound := by
    dsimp [bound]
    exact le_sup_of_le_right le_rfl
  have hbound_lt_sigma : bound < Cardinal.mk σ := by
    dsimp [σ]
    rw [Cardinal.mk_set, Cardinal.mk_toType, Cardinal.card_ord]
    exact Cardinal.cantor bound
  have hκ₁_lt : κ₁ < Cardinal.mk σ :=
    lt_of_le_of_lt hbound_le_κ₁ hbound_lt_sigma
  have hκ₂_lt : κ₂ < Cardinal.mk σ :=
    lt_of_le_of_lt hbound_le_κ₂ hbound_lt_sigma
  have haleph0_le_sigma : Cardinal.aleph0 ≤ Cardinal.mk σ :=
    le_of_lt (lt_of_le_of_lt hbound_le_aleph0 hbound_lt_sigma)
  have hσ_infinite : Infinite σ :=
    Cardinal.aleph0_le_mk_iff.mp haleph0_le_sigma
  let F : Type u := FractionRing (MvPolynomial σ k)
  let K : Type u := AlgebraicClosure F
  -- Local instance justification (defeq pin): expose the canonical field structure on `F`.
  letI : Field F := inferInstance
  -- Local instance justification (defeq pin): expose the canonical `k`-algebra structure on `F`.
  letI : Algebra k F := inferInstance
  -- Local instance justification (defeq pin): expose the canonical field structure on `K`.
  letI : Field K := inferInstance
  -- Local instance justification (defeq pin): expose the algebraic-closure algebra structure.
  letI : Algebra F K := inferInstance
  -- Local instance justification (instance diamond): fix the composite `k`-algebra structure on `K`.
  letI : Algebra k K := Algebra.compHom K (algebraMap k F)
  have hk_le_sigma : Cardinal.mk k ≤ Cardinal.mk σ :=
    le_of_lt (lt_of_le_of_lt (by
      dsimp [bound]
      exact le_sup_of_le_left <| le_sup_of_le_left <| le_sup_of_le_left le_rfl) hbound_lt_sigma)
  have hk_le_sigma_sup : Cardinal.mk k ≤ Cardinal.mk σ ⊔ Cardinal.aleph0 :=
    hk_le_sigma.trans le_sup_left
  have hF_card : Cardinal.mk F = Cardinal.mk σ := by
    dsimp [F]
    rw [FractionRing.cardinalMk, MvPolynomial.cardinalMk_eq_max]
    calc
      Cardinal.mk k ⊔ Cardinal.mk σ ⊔ Cardinal.aleph0 =
          Cardinal.mk σ ⊔ Cardinal.aleph0 := by
        rw [sup_eq_right.mpr hk_le_sigma]
      _ = Cardinal.mk σ := sup_eq_left.mpr haleph0_le_sigma
  have hFK : Cardinal.mk F ≤ Cardinal.mk K :=
    Cardinal.mk_le_of_injective (FaithfulSMul.algebraMap_injective F K)
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  constructor
  · exact lt_of_lt_of_le (by simpa [hF_card] using hκ₁_lt) hFK
  · exact lt_of_lt_of_le (by simpa [hF_card] using hκ₂_lt) hFK

end Field
