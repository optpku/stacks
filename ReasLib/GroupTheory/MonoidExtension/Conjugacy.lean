module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.GroupAction.Quotient
public import ReasLib.GroupTheory.MonoidExtension.Nat

/-!
# Centralizer cardinalities and conjugacy-class counting
-/

@[expose] public section

noncomputable section

universe u v w

namespace NatMonoidExtension

variable {G : Type v} {Γ : Type w} [Group G] [Monoid Γ] (S : NatMonoidExtension G Γ)

/-- Kernel-group conjugate degree-one elements have centralizers of equal cardinality. -/
theorem card_centralizer_eq_of_isGConj {γ γ' : S.degreeOne}
    (h : MulAction.orbitRel G S.degreeOne γ γ') :
    Nat.card (S.centralizer γ.val) = Nat.card (S.centralizer γ'.val) := by
  sorry

/-- The centralizer cardinality as a function on degree-one kernel-group conjugacy classes. -/
def cardCentralizer : S.DegreeOneGConjClass → ℕ :=
  Quotient.lift (fun γ : S.degreeOne ↦ Nat.card (S.centralizer γ.val))
    fun _ _ h ↦ S.card_centralizer_eq_of_isGConj h

/-- The centralizer cardinality of a class is computed from any representative. -/
theorem cardCentralizer_mk (γ : S.degreeOne) :
    cardCentralizer S (Quotient.mk (MulAction.orbitRel G S.degreeOne) γ) =
      Nat.card (S.centralizer γ.val) := rfl

/-- If the finite kernel group's order is a coefficient unit, every centralizer order is a unit. -/
theorem isUnit_cardCentralizer {Λ : Type u} [Ring Λ] [Finite G]
    (hG : IsUnit (Nat.card G : Λ)) (c : S.DegreeOneGConjClass) :
    IsUnit (S.cardCentralizer c : Λ) := by
  sorry

variable {E : Type w} [Group E] (T : GroupExtension G E (Multiplicative ℤ))

/-- The inverse centralizer orders of degree-one conjugacy classes sum to one over a field
in which the finite kernel group's order is invertible. -/
theorem one_eq_sum_inv_cardCentralizer {Λ : Type u} [Field Λ] [Finite G]
    (hG : IsUnit (Nat.card G : Λ)) :
    (1 : Λ) = ∑ᶠ c : (ofGroupExtension T).DegreeOneGConjClass,
      ((ofGroupExtension T).cardCentralizer c : Λ)⁻¹ := by
  sorry

/-- In prime characteristic not dividing the kernel group's order, the inverse centralizer
orders of degree-one conjugacy classes sum to one. -/
theorem one_eq_sum_inv_cardCentralizer_zmod [Finite G] {ℓ : ℕ} [Fact ℓ.Prime]
    (hG : IsUnit (Nat.card G : ZMod ℓ)) :
    (1 : ZMod ℓ) = ∑ᶠ c : (ofGroupExtension T).DegreeOneGConjClass,
      ((ofGroupExtension T).cardCentralizer c : ZMod ℓ)⁻¹ :=
  one_eq_sum_inv_cardCentralizer T hG

end NatMonoidExtension
