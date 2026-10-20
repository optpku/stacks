/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The quotient of a product by the product of additive subgroups. -/

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

variable {ι : Type*} (A : ι → Type*) [∀ i, AddCommGroup (A i)]
    (N : ∀ i, AddSubgroup (A i))

/-- The actual coordinatewise quotient homomorphism. -/
def piQuotientMap : (∀ i, A i) →+ ∀ i, A i ⧸ N i where
  toFun a i := QuotientAddGroup.mk' (N i) (a i)
  map_zero' := by ext i; exact map_zero (QuotientAddGroup.mk' (N i))
  map_add' a b := by ext i; exact map_add (QuotientAddGroup.mk' (N i)) (a i) (b i)

theorem piQuotientMap_surjective : Function.Surjective (piQuotientMap A N) := by
  intro a
  refine ⟨fun i ↦ Quotient.out (a i), ?_⟩
  funext i
  exact Quotient.out_eq (a i)

theorem piQuotientMap_ker :
    AddSubgroup.pi Set.univ N = (piQuotientMap A N).ker := by
  ext a
  simp [AddSubgroup.mem_pi, AddMonoidHom.mem_ker, piQuotientMap, funext_iff]

/-- This inverse uses representatives of actual quotient classes, with its
surjectivity and kernel equality proved above. It is not an assumed isomorphism. -/
noncomputable def quotientPi :
    (∀ i, A i) ⧸ AddSubgroup.pi Set.univ N ≃+ ∀ i, A i ⧸ N i :=
  QuotientAddGroup.liftEquiv (AddSubgroup.pi Set.univ N)
    (piQuotientMap_surjective A N) (piQuotientMap_ker A N)

@[simp] theorem quotientPi_mk (a : ∀ i, A i) (i : ι) :
    quotientPi A N (QuotientAddGroup.mk' (AddSubgroup.pi Set.univ N) a) i =
      QuotientAddGroup.mk' (N i) (a i) := rfl

end AlgebraicGeometry.AlgebraicSpace.IntersectionTheory
