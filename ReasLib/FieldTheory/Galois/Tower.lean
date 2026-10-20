/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w

namespace FieldExtension

section

variable (K : Type u) (M : Type v) (L : Type w)
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]

/-- The natural inclusion `Gal(L/M) →* Gal(L/K)` in a tower of fields `L/M/K`, obtained by
restricting scalars along `K → M`. -/
def galRestrictScalarsHom : Gal(L/M) →* Gal(L/K) :=
  MonoidHom.mk' (fun σ ↦ σ.restrictScalars K) fun _ _ ↦ AlgEquiv.ext fun _ ↦ rfl

/-- The Galois restriction-of-scalars homomorphism acts as the underlying automorphism of `L`. -/
@[simp]
theorem galRestrictScalarsHom_apply (σ : Gal(L/M)) (x : L) :
    galRestrictScalarsHom K M L σ x = σ x :=
  rfl

/-- The inclusion `Gal(L/M) →* Gal(L/K)` is injective. -/
theorem galRestrictScalarsHom_injective :
    Function.Injective (galRestrictScalarsHom K M L) := fun _ _ h ↦
  AlgEquiv.restrictScalars_injective K h

/-- If `M/K` is normal, restriction `Gal(L/K) →* Gal(M/K)` is surjective. -/
theorem restrictNormalHomSurjective [Normal K L] [Normal K M] :
    Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) :=
  AlgEquiv.restrictNormalHom_surjective L

/-- The defining commutative square of `AlgEquiv.restrictNormalHom` in an abstract field tower. -/
private theorem algebraMap_restrictNormalHom_apply [Normal K M] (σ : Gal(L/K)) (x : M) :
    algebraMap M L (AlgEquiv.restrictNormalHom M σ x) = σ (algebraMap M L x) :=
  AlgEquiv.restrictNormal_commutes σ M x

/-- The range of `Gal(L/M) →* Gal(L/K)` is the kernel of restriction to `Gal(M/K)`. -/
theorem galRestrictScalarsHom_range_eq_restrictNormalHom_ker [Normal K M] :
    (galRestrictScalarsHom K M L).range =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker := by
  ext σ
  simp only [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨τ, rfl⟩
    refine AlgEquiv.ext fun x ↦ (algebraMap M L).injective ?_
    rw [algebraMap_restrictNormalHom_apply, AlgEquiv.one_apply, galRestrictScalarsHom_apply]
    exact τ.commutes x
  · intro hσ
    have hfix : ∀ x : M, σ (algebraMap M L x) = algebraMap M L x := fun x ↦ by
      rw [← algebraMap_restrictNormalHom_apply K M L σ x, hσ, AlgEquiv.one_apply]
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) hfix, AlgEquiv.ext fun _ ↦ rfl⟩

/-- The Galois group `Gal(L/K)` is finite when `L/K` is finite. -/
theorem finiteGaloisGroup [FiniteDimensional K L] : Finite Gal(L/K) :=
  inferInstance

/-- The Galois group `Gal(L/M)` is finite when `L/K` is finite. -/
theorem finiteGaloisGroupTowerTop [FiniteDimensional K L] : Finite Gal(L/M) :=
  Finite.of_injective _ (galRestrictScalarsHom_injective K M L)

/-- The Galois group `Gal(M/K)` is finite when `L/K` is finite and both extensions are normal. -/
theorem finiteGaloisGroupTowerBottom [FiniteDimensional K L] [Normal K L] [Normal K M] :
    Finite Gal(M/K) :=
  Finite.of_surjective _ (restrictNormalHomSurjective K M L)

/-- A finite Galois tower `L/M/K` gives an exact sequence
`1 → Gal(L/M) → Gal(L/K) → Gal(M/K) → 1`, expressed by finite group types, an injective
inclusion, equality of its range with the restriction kernel, and a surjective restriction map. -/
theorem galoisGroupTowerShortExact [FiniteDimensional K L] [IsGalois K L] [IsGalois K M] :
    (Finite Gal(L/M) ∧ Finite Gal(L/K) ∧ Finite Gal(M/K)) ∧
      Function.Injective (galRestrictScalarsHom K M L) ∧
      (galRestrictScalarsHom K M L).range =
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M).ker ∧
      Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M) :=
  ⟨⟨finiteGaloisGroupTowerTop K M L, finiteGaloisGroup K L,
      finiteGaloisGroupTowerBottom K M L⟩,
    galRestrictScalarsHom_injective K M L,
    galRestrictScalarsHom_range_eq_restrictNormalHom_ker K M L,
    restrictNormalHomSurjective K M L⟩

end

end FieldExtension
