/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.BaseChange
public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars

/-!
# Exterior powers and base change

The forward comparison extends the alternating product of pure tensors. Its
inverse restricts the explicit exterior-algebra comparison to a homogeneous
degree, using `ExteriorAlgebra.liftAlternating` for the degree projection.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace exteriorPower

/-- Apply a specified linear equivalence to every entry of an exterior product. -/
noncomputable def mapEquiv {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (p : ℕ) (equiv : M ≃ₗ[R] N) :
    (⋀[R]^p M) ≃ₗ[R] ⋀[R]^p N where
  toFun := map p equiv.toLinearMap
  invFun := map p equiv.symm.toLinearMap
  map_add' := (map p equiv.toLinearMap).map_add
  map_smul' := (map p equiv.toLinearMap).map_smul
  left_inv vector := by
    change ((map p equiv.symm.toLinearMap).comp (map p equiv.toLinearMap)) vector = vector
    rw [← map_comp]
    have composition : equiv.symm.toLinearMap.comp equiv.toLinearMap = LinearMap.id := by
      ext entry
      exact equiv.symm_apply_apply entry
    rw [composition, map_id]
    rfl
  right_inv vector := by
    change ((map p equiv.toLinearMap).comp (map p equiv.symm.toLinearMap)) vector = vector
    rw [← map_comp]
    have composition : equiv.toLinearMap.comp equiv.symm.toLinearMap = LinearMap.id := by
      ext entry
      exact equiv.apply_symm_apply entry
    rw [composition, map_id]
    rfl

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

/-- Projection from the exterior algebra onto its specified homogeneous degree. -/
noncomputable def degreeProjection (p : ℕ) :
    ExteriorAlgebra R M →ₗ[R] ⋀[R]^p M :=
  ExteriorAlgebra.liftAlternating (Function.update 0 p (ιMulti R p))

/-- The homogeneous projection fixes the corresponding exterior generators. -/
@[simp]
theorem degreeProjection_ιMulti (p : ℕ) (vectors : Fin p → M) :
    degreeProjection R M p (ExteriorAlgebra.ιMulti R p vectors) = ιMulti R p vectors := by
  simp [degreeProjection]

/-- The canonical scalar-extension map on exterior powers. -/
noncomputable def baseChangeHom (p : ℕ) :
    S ⊗[R] (⋀[R]^p M) →ₗ[S] ⋀[S]^p (S ⊗[R] M) := by
  letI := RestrictScalars.moduleOrig R S (⋀[S]^p (S ⊗[R] M))
  exact
    (restrictScalarsMap (R := R) (S := S) p (TensorProduct.mk R S M 1)).liftBaseChange S

/-- The inverse comparison, given by the exterior-algebra inverse followed by
the base change of the homogeneous projection. -/
noncomputable def baseChangeInv (p : ℕ) :
    (⋀[S]^p (S ⊗[R] M)) →ₗ[S] S ⊗[R] (⋀[R]^p M) :=
  ((degreeProjection R M p).baseChange S).comp
    (((TensorProduct.isBaseChange R M S).exteriorAlgebraEquiv).symm.toLinearMap.comp
      (Submodule.subtype (⋀[S]^p (S ⊗[R] M))))

/-- Exterior powers commute with arbitrary scalar extension, with both maps
specified independently of the inverse laws. -/
noncomputable def baseChangeEquiv (p : ℕ) :
    S ⊗[R] (⋀[R]^p M) ≃ₗ[S] ⋀[S]^p (S ⊗[R] M) where
  toFun := baseChangeHom R S M p
  invFun := baseChangeInv R S M p
  map_add' := (baseChangeHom R S M p).map_add
  map_smul' := (baseChangeHom R S M p).map_smul
  left_inv := by sorry
  right_inv := by sorry

/-- The forward comparison on exterior generators. -/
theorem baseChangeEquiv_tmul_ιMulti (p : ℕ) (scalar : S) (vectors : Fin p → M) :
    baseChangeEquiv R S M p (scalar ⊗ₜ[R] ιMulti R p vectors) =
      scalar • ιMulti S p (fun index ↦ 1 ⊗ₜ[R] vectors index) := by
  sorry

/-- The inverse comparison on exterior generators with pure-tensor entries. -/
theorem baseChangeEquiv_symm_ιMulti (p : ℕ) (scalars : Fin p → S)
    (vectors : Fin p → M) :
    (baseChangeEquiv R S M p).symm
        (ιMulti S p (fun index ↦ scalars index ⊗ₜ[R] vectors index)) =
      (∏ index, scalars index) ⊗ₜ[R] ιMulti R p vectors := by
  sorry

end exteriorPower
