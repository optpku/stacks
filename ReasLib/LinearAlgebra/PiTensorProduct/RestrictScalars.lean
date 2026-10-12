/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.RestrictScalars

/-!
# Restriction of Scalars for Indexed Tensor Products

The codomain uses Mathlib's `RestrictScalars` alias.  Consequently callers do
not need to install a competing module action on the raw tensor product.

The API is indexed by an arbitrary nonempty type and an arbitrary family of
linear maps; tensor powers are the constant-family specialization.

@stack 0H1C
-/

@[expose] public section

open scoped TensorProduct

namespace PiTensorProduct

universe uι uR uS uM uN

variable {ι : Type uι}
variable {R : Type uR} {S : Type uS}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {M : ι → Type uM} {N : ι → Type uN}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module S (N i)]
variable [∀ i, Module R (N i)] [∀ i, IsScalarTower R S (N i)]

/-- The indexed tensor-product map induced by an `R`-linear family into
`S`-modules, with the target viewed through the canonical restriction of
scalars. -/
@[stacks 0H1C "indexed tensor-product scalar restriction"]
noncomputable def restrictScalarsMap (f : ∀ i, M i →ₗ[R] N i) :
    (⨂[R] i, M i) →ₗ[R] RestrictScalars R S (⨂[S] i, N i) := by
  exact PiTensorProduct.lift
    (({ toFun := PiTensorProduct.tprod S
        map_update_add' := by
          intro _ m i x y
          exact (PiTensorProduct.tprod S).map_update_add m i x y
        map_update_smul' := by
          intro _ m i r x
          change PiTensorProduct.tprod S (Function.update m i (r • x)) =
            algebraMap R S r • PiTensorProduct.tprod S (Function.update m i x)
          rw [← IsScalarTower.algebraMap_smul S r x]
          exact (PiTensorProduct.tprod S).map_update_smul m i (algebraMap R S r) x } :
      MultilinearMap R N (RestrictScalars R S (⨂[S] i, N i))).compLinearMap f)

/-- `restrictScalarsMap` acts entrywise on pure tensors. -/
@[simp, stacks 0H1C "indexed tensor-product scalar restriction on pure tensors"]
theorem restrictScalarsMap_tprod (f : ∀ i, M i →ₗ[R] N i) (m : ∀ i, M i) :
    restrictScalarsMap (R := R) (S := S) f (tprod R m) =
      (tprod S (fun i ↦ f i (m i)) : RestrictScalars R S (⨂[S] i, N i)) := sorry

/-- A pointwise-surjective family induces a surjection on nonempty indexed
tensor products after changing the coefficient ring. -/
@[stacks 0H1C "surjective indexed tensor-product scalar restriction"]
theorem restrictScalarsMap_surjective [Nonempty ι]
    (f : ∀ i, M i →ₗ[R] N i) (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (restrictScalarsMap (R := R) (S := S) f) := sorry

namespace RestrictScalars

section Bundled

variable {M : ι → Type uM} {N : ι → Type uN}
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module S (N i)]

/-- The indexed tensor-product map induced by a family whose codomains are
already bundled as canonical restrictions of scalars.

Unlike `PiTensorProduct.restrictScalarsMap`, this is the structure-minimal
entry point: no second module action or scalar-tower instance is required on
the raw target carriers. -/
@[stacks 0H1C "bundled indexed tensor-product scalar restriction"]
noncomputable def map
    (f : ∀ i, M i →ₗ[R] _root_.RestrictScalars R S (N i)) :
    (⨂[R] i, M i) →ₗ[R] _root_.RestrictScalars R S (⨂[S] i, N i) := by
  -- Local instance justification (defeq pin): the tensor adapter requires the original S-actions on the restricted target aliases.
  letI : ∀ i, Module S (_root_.RestrictScalars R S (N i)) :=
    fun i ↦ _root_.RestrictScalars.moduleOrig R S (N i)
  exact PiTensorProduct.restrictScalarsMap (R := R) (S := S)
    (N := fun i ↦ _root_.RestrictScalars R S (N i)) f

/-- `map` acts entrywise on pure tensors. -/
@[simp, stacks 0H1C "bundled tensor restriction on pure tensors"]
theorem map_tprod
    (f : ∀ i, M i →ₗ[R] _root_.RestrictScalars R S (N i))
    (m : ∀ i, M i) :
    map (R := R) (S := S) f (tprod R m) =
      (tprod S (fun i ↦ f i (m i)) :
        _root_.RestrictScalars R S (⨂[S] i, N i)) := by
  -- Local instance justification (defeq pin): the generator formula must use the original S-actions on the restricted target aliases.
  letI : ∀ i, Module S (_root_.RestrictScalars R S (N i)) :=
    fun i ↦ _root_.RestrictScalars.moduleOrig R S (N i)
  rw [map]
  exact PiTensorProduct.restrictScalarsMap_tprod (R := R) (S := S)
    (N := fun i ↦ _root_.RestrictScalars R S (N i)) f m

/-- A pointwise-surjective bundled family induces a surjection on a nonempty
indexed tensor product. -/
@[stacks 0H1C "surjective bundled tensor restriction"]
theorem map_surjective [Nonempty ι]
    (f : ∀ i, M i →ₗ[R] _root_.RestrictScalars R S (N i))
    (hf : ∀ i, Function.Surjective (f i)) :
    Function.Surjective (map (R := R) (S := S) f) := by
  -- Local instance justification (defeq pin): the surjectivity adapter requires the original S-actions on the restricted target aliases.
  letI : ∀ i, Module S (_root_.RestrictScalars R S (N i)) :=
    fun i ↦ _root_.RestrictScalars.moduleOrig R S (N i)
  exact PiTensorProduct.restrictScalarsMap_surjective (R := R) (S := S)
    (N := fun i ↦ _root_.RestrictScalars R S (N i)) f hf

end Bundled

end RestrictScalars

section ScalarTower

variable {P : ι → Type uM}
variable [∀ i, AddCommMonoid (P i)]
variable [∀ i, Module R (P i)] [∀ i, Module S (P i)]
variable [∀ i, IsScalarTower R S (P i)]

/-- The canonical comparison from an indexed tensor product over `R` to the
same indexed tensor product over `S`. -/
@[stacks 0H1C "tensor-power scalar-restriction comparison"]
noncomputable def scalarTowerMap :
    (⨂[R] i, P i) →ₗ[R] RestrictScalars R S (⨂[S] i, P i) :=
  restrictScalarsMap (R := R) (S := S) (fun _ ↦ LinearMap.id)

/-- `scalarTowerMap` preserves pure tensors. -/
@[simp, stacks 0H1C "scalar-tower comparison on pure tensors"]
theorem scalarTowerMap_tprod (m : ∀ i, P i) :
    scalarTowerMap (R := R) (S := S) (P := P) (tprod R m) =
      (tprod S m : RestrictScalars R S (⨂[S] i, P i)) := by
  simp [scalarTowerMap]

/-- In nonzero tensor degree, the scalar-tower comparison is surjective. -/
@[stacks 0H1C "surjective scalar-tower tensor comparison"]
theorem scalarTowerMap_surjective [Nonempty ι] :
    Function.Surjective (scalarTowerMap (R := R) (S := S) (P := P)) :=
  restrictScalarsMap_surjective (R := R) (S := S)
    (fun _ ↦ LinearMap.id) (fun _ ↦ Function.surjective_id)

end ScalarTower

/-- Restriction of scalars for an entrywise map is the ordinary indexed tensor-product map
followed by the scalar-tower comparison. -/
@[stacks 0H1C "factorization of indexed tensor-product scalar restriction"]
theorem restrictScalarsMap_factor (f : ∀ i, M i →ₗ[R] N i) :
    restrictScalarsMap (R := R) (S := S) f =
      (scalarTowerMap (R := R) (S := S) (P := N)).comp (PiTensorProduct.map f) := by
  apply PiTensorProduct.ext
  ext m
  simp

end PiTensorProduct
