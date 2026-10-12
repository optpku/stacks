/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

universe u v

namespace LinearMap.Frobenius

variable {k : Type u} {V : Type v} {p : ℕ}
variable [Field k] [Fact p.Prime] [CharP k p] [AddCommGroup V] [Module k V]

/-- The additive endomorphism `F - 1` associated to a Frobenius-semilinear endomorphism. -/
def subId (F : V →ₛₗ[_root_.frobenius k p] V) : V →+ V :=
  F.toAddMonoidHom - AddMonoidHom.id V

/-- The additive endomorphism `subId F` acts by `v ↦ F v - v`. -/
theorem subId_apply (F : V →ₛₗ[_root_.frobenius k p] V) (v : V) :
    subId F v = F v - v := sorry

/-- The kernel of `subId F` is the additive subgroup of fixed points of `F`. -/
theorem mem_subId_ker_iff (F : V →ₛₗ[_root_.frobenius k p] V) (v : V) :
    v ∈ (subId F).ker ↔ F v = v := sorry

/-- Every element of the fixed-point kernel of a Frobenius-semilinear map is killed by `p`. -/
theorem subId_ker_nsmul (F : V →ₛₗ[_root_.frobenius k p] V)
    (x : (subId F).ker) : p • x = 0 := sorry

/-- The canonical `ZMod p`-module structure on the fixed-point kernel of `F`. -/
instance subIdKerModule (F : V →ₛₗ[_root_.frobenius k p] V) :
    Module (ZMod p) (subId F).ker :=
  AddCommGroup.zmodModule (subId_ker_nsmul F)

variable [IsAlgClosed k] [FiniteDimensional k V]

/-- A Frobenius-semilinear endomorphism of a finite-dimensional vector space over an
algebraically closed field has surjective difference from the identity. -/
theorem subId_surjective (F : V →ₛₗ[_root_.frobenius k p] V) :
    Function.Surjective (subId F) := sorry

/-- The fixed-point kernel of a Frobenius-semilinear endomorphism is finite-dimensional
over `ZMod p`. -/
instance kerFiniteDimensional (F : V →ₛₗ[_root_.frobenius k p] V) :
    FiniteDimensional (ZMod p) (subId F).ker := sorry

/-- The `ZMod p`-dimension of the fixed-point kernel is at most the dimension of the
ambient vector space over `k`. -/
theorem kerFinrankLe (F : V →ₛₗ[_root_.frobenius k p] V) :
    Module.finrank (ZMod p) (subId F).ker ≤ Module.finrank k V := sorry

end LinearMap.Frobenius
