module

public import Mathlib.LinearAlgebra.TensorProduct.Map
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Map
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Prod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of binary direct sums

The forward determinant product map is defined for arbitrary modules by the exterior-algebra
direct-sum equivalence and the determinant kernel's universal property.  For finite projective
modules, its comparison with the tensor range provides separate infrastructure for proving that
the map is an isomorphism without using such a proof to define the forward map.
@stack 0FJB
-/

@[expose] public section

noncomputable section

open scoped TensorProduct Module.Determinant

universe u v w

namespace Module.Determinant

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable (N : Type w) [AddCommGroup N] [Module R N]

/-- The canonical map from the tensor product of determinant submodules into the tensor product
of the ambient exterior algebras. -/
@[stacks 0FJB "tensor map on determinant submodules"]
abbrev tensorMap :
    det[R](M) ⊗[R] det[R](N) →ₗ[R]
      ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N :=
  TensorProduct.mapIncl det[R](M) det[R](N)

/-- The ambient exterior-algebra map underlying the determinant product map. -/
@[stacks 0FJB "ambient determinant product map"]
noncomputable def prodAmbientMap :
    det[R](M) ⊗[R] det[R](N) →ₗ[R] ExteriorAlgebra R (M × N) :=
  (ExteriorAlgebra.prodEquiv R M N).symm.toLinearMap.comp (tensorMap R M N)

/-- The ambient determinant product map takes values in the determinant submodule of the product
module. -/
@[stacks 0FJB "ambient determinant product map lands in the determinant"]
theorem range_prodAmbientMap_le :
    LinearMap.range (prodAmbientMap R M N) ≤ det[R](M × N) := sorry

/-- The canonical determinant product map, defined for arbitrary modules. -/
@[stacks 0FJB "determinant product map"]
noncomputable def prodMap :
    det[R](M) ⊗[R] det[R](N) →ₗ[R] det[R](M × N) :=
  @Module.Determinant.lift R _ (M × N) _ _
    (det[R](M) ⊗[R] det[R](N)) _ _
      (prodAmbientMap R M N) (range_prodAmbientMap_le R M N)

/-- The determinant product map recovers its ambient exterior-algebra map after inclusion. -/
@[stacks 0FJB "determinant product map inclusion equation"]
theorem prodMap_ι :
    (ι R (M × N)).comp (prodMap R M N) = prodAmbientMap R M N := sorry

/-- The ambient image of a pure determinant tensor is the wedge product of the two canonical
product inclusions. -/
@[simp, stacks 0FJB "pure tensor formula for the determinant product map"]
theorem ι_prodMap_tmul (x : det[R](M)) (y : det[R](N)) :
    ι R (M × N) (prodMap R M N (x ⊗ₜ[R] y)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (x : ExteriorAlgebra R M) *
        ExteriorAlgebra.map (LinearMap.inr R M N) (y : ExteriorAlgebra R N) := sorry

/-- The image of the tensor product of determinant submodules in the ambient tensor product. -/
@[stacks 0FJB "tensor range of determinant submodules"]
abbrev tensorRange :
    Submodule R (ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N) :=
  LinearMap.range (tensorMap R M N)

/-- The canonical inclusion of the determinant tensor range into the ambient tensor product. -/
@[stacks 0FJB "determinant tensor range inclusion"]
abbrev tensorRangeι :
    tensorRange R M N →ₗ[R] ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N :=
  Submodule.subtype (tensorRange R M N)

/-- The canonical surjection from the tensor product of determinant submodules onto its range. -/
@[stacks 0FJB "lift to the determinant tensor range"]
def tensorLift : det[R](M) ⊗[R] det[R](N) →ₗ[R] tensorRange R M N :=
  (tensorMap R M N).codRestrict (tensorRange R M N)
    (LinearMap.mem_range_self (tensorMap R M N))

/-- The tensor-range lift recovers the canonical ambient tensor map after inclusion. -/
@[stacks 0FJB "determinant tensor range lift equation"]
theorem tensorLift_ι :
    (tensorRangeι R M N).comp (tensorLift R M N) = tensorMap R M N := sorry

/-- The canonical map from the tensor product of determinant submodules onto its range is
surjective. -/
theorem tensorLift_surjective : Function.Surjective (tensorLift R M N) := sorry

/-- For finite projective modules, the direct-sum exterior-algebra equivalence carries the
determinant of `M × N` onto the tensor range of the two determinant submodules. -/
@[stacks 0FJB "determinant of a direct sum as a tensor range"]
theorem prodEquiv_map_eq_tensorRange
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    Submodule.map (ExteriorAlgebra.prodEquiv R M N).toLinearMap det[R](M × N) =
      tensorRange R M N := sorry

/-- The determinant of a direct sum of finite projective modules is explicitly equivalent to the
range of the tensor product of their determinant submodules. -/
@[stacks 0FJB "determinant direct-sum range equivalence"]
noncomputable def prodRangeIso
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    det[R](M × N) ≃ₗ[R] tensorRange R M N :=
  (ExteriorAlgebra.prodEquiv R M N).ofSubmodules
    det[R](M × N) (tensorRange R M N) (prodEquiv_map_eq_tensorRange R M N)

/-- The direct-sum determinant range equivalence is the restriction of the ambient exterior
direct-sum equivalence. -/
@[stacks 0FJB "determinant direct-sum range inclusion equation"]
theorem prodRangeIso_ι
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    (tensorRangeι R M N).comp (prodRangeIso R M N).toLinearMap =
      (ExteriorAlgebra.prodEquiv R M N).toLinearMap.comp (ι R (M × N)) := sorry

/-- On pure determinant tensors, the inverse direct-sum comparison is characterized by the
wedge product of the two canonical exterior-algebra inclusions. -/
@[stacks 0FJB "inverse determinant direct-sum range formula"]
theorem prodRangeIso_inv_tmul
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (x : det[R](M)) (y : det[R](N)) :
    ι R (M × N) ((prodRangeIso R M N).symm (tensorLift R M N (x ⊗ₜ[R] y))) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (x : ExteriorAlgebra R M) *
        ExteriorAlgebra.map (LinearMap.inr R M N) (y : ExteriorAlgebra R N) := sorry

end Module.Determinant
