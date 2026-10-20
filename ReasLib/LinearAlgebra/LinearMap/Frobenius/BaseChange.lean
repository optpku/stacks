module

public import ReasLib.LinearAlgebra.LinearMap.Frobenius
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

universe u u' v

open TensorProduct

namespace LinearMap.Frobenius

section

variable {k : Type u} {V : Type v} {p : ℕ}
variable [Field k] [Fact p.Prime] [CharP k p] [AddCommGroup V] [Module k V]
variable (k' : Type u') [Field k'] [Algebra k k'] [CharP k' p]

/-- The Frobenius-semilinear endomorphism induced by `F` after extending scalars from `k`
to `k'`, sending `a ⊗ₜ v` to `(a ^ p) ⊗ₜ F v`. -/
def baseChange (F : V →ₛₗ[_root_.frobenius k p] V) :
    k' ⊗[k] V →ₛₗ[_root_.frobenius k' p] k' ⊗[k] V where
  toFun := TensorProduct.map (_root_.LinearMap.frobenius k k' p) F
  map_add' := (TensorProduct.map (_root_.LinearMap.frobenius k k' p) F).map_add
  map_smul' := sorry

/-- The induced map sends elementary tensors to `(a ^ p) ⊗ₜ F v`. -/
theorem baseChange_tmul (F : V →ₛₗ[_root_.frobenius k p] V) (a : k') (v : V) :
    baseChange k' F (a ⊗ₜ v) = (a ^ p) ⊗ₜ F v := sorry

/-- On pure tensors `1 ⊗ₜ v`, the induced map is `1 ⊗ₜ F v`. -/
theorem baseChange_one_tmul (F : V →ₛₗ[_root_.frobenius k p] V) (v : V) :
    baseChange k' F (1 ⊗ₜ v) = 1 ⊗ₜ F v := sorry

/-- If `v` is fixed by `F`, then `1 ⊗ₜ v` is fixed by the induced map. -/
theorem one_tmul_mem_subId_ker (F : V →ₛₗ[_root_.frobenius k p] V) (x : (subId F).ker) :
    (1 : k') ⊗ₜ x.val ∈ (subId (baseChange k' F)).ker := sorry

/-- The canonical `ZMod p`-linear comparison of fixed-point kernels, sending `v` to `1 ⊗ₜ v`. -/
def subIdKerBaseChange (F : V →ₛₗ[_root_.frobenius k p] V) :
    (subId F).ker →ₗ[ZMod p] (subId (baseChange k' F)).ker :=
  (((TensorProduct.mk k k' V 1).toAddMonoidHom.comp (subId F).ker.subtype).codRestrict
    (subId (baseChange k' F)).ker (one_tmul_mem_subId_ker k' F)).toZModLinearMap p

/-- The comparison map is the pure tensor `1 ⊗ₜ v` on underlying vectors. -/
theorem subIdKerBaseChange_apply (F : V →ₛₗ[_root_.frobenius k p] V) (x : (subId F).ker) :
    (subIdKerBaseChange k' F x).val = (1 : k') ⊗ₜ x.val := sorry

end

variable {k : Type u} {V : Type v} {p : ℕ}
variable [Field k] [IsAlgClosed k] [Fact p.Prime] [CharP k p]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- For a Frobenius-semilinear endomorphism of a finite-dimensional vector space over an
algebraically closed field, the canonical `ZMod p`-linear comparison of fixed-point kernels
is bijective after an algebraically closed field extension. -/
theorem subIdKerBaseChange_bijective
    (k' : Type u') [Field k'] [IsAlgClosed k'] [Algebra k k'] [CharP k' p]
    (F : V →ₛₗ[_root_.frobenius k p] V) :
    Function.Bijective (subIdKerBaseChange k' F) := sorry

end LinearMap.Frobenius
