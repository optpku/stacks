/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.ShortExact
public import ReasLib.LinearAlgebra.Determinant.Projective
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinant comparison for a split binary sum

The split rows `0 ⟶ M ⟶ M × N ⟶ N ⟶ 0` and its transpose are a recurring source of
determinant-line comparison maps.  This leaf owns their canonical equivalences and the signed
tensor switch.  The public square is stated as an equality of linear maps, which is the compact
form consumed by later algebraic arguments; a `CommSq` view can be added at a category boundary.

@stack 0FJE
-/

@[expose] public section

noncomputable section

open scoped Module.Determinant TensorProduct

universe u v w

namespace Module.Determinant.Split

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Projective R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
  [Module.Finite R N] [Module.Projective R N]

/-- The determinant-line equivalence attached to the split row `0 ⟶ M ⟶ M × N ⟶ N ⟶ 0`. -/
@[stacks 0FJE "determinant equivalence for a split binary sum"]
noncomputable def splitIso (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    (det[R](M) ⊗[R] det[R](N)) ≃ₗ[R] det[R](M × N) :=
  Module.Determinant.tensorIsoOfExact
    (LinearMap.inl R M N) (LinearMap.snd R M N)
    LinearMap.inl_injective LinearMap.snd_surjective Function.Exact.inl_snd

/-- The wedge formula characterizing `splitIso`. -/
@[stacks 0FJE "split determinant wedge formula"]
theorem splitIso_spec
    (x : det[R](M)) (y : det[R](N)) (z : ExteriorAlgebra R (M × N))
    (hz : ExteriorAlgebra.map (LinearMap.snd R M N) z =
      (y : ExteriorAlgebra R N)) :
    (splitIso R M N (x ⊗ₜ[R] y) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (x : ExteriorAlgebra R M) * z := sorry
-- Proof strategy: unfold `splitIso` and apply `tensorIsoOfExact_spec` to the canonical exact pair
-- `LinearMap.inl` and `LinearMap.snd`.

/-- The scalar used by the Koszul switch: the projective determinant of `-id` on `M ⊗[R] N`. -/
@[stacks 0FJE "determinant sign of the tensor switch"]
noncomputable def switchSign (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] : R :=
  LinearMap.projectiveDet
    (-LinearMap.id : (M ⊗[R] N) →ₗ[R] M ⊗[R] N)

/-- The signed symmetry map on the tensor product of determinant lines. -/
@[stacks 0FJE "signed tensor symmetry on determinant lines"]
noncomputable def switchMap (R : Type u) (M : Type v) (N : Type w)
    [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] :
    det[R](M) ⊗[R] det[R](N) →ₗ[R] det[R](N) ⊗[R] det[R](M) :=
  (TensorProduct.comm R (det[R](M)) (det[R](N))).toLinearMap.comp
    (Module.toModuleEnd R (det[R](M) ⊗[R] det[R](N)) (switchSign R M N))

/-- Swapping the two summands intertwines the split determinant comparisons up to `switchMap`. -/
@[stacks 0FJE "determinant split-sum symmetry square"]
theorem commutes :
    (Module.Determinant.mapIso (LinearEquiv.prodComm R M N)).toLinearMap.comp
        (splitIso R M N).toLinearMap =
      (splitIso R N M).toLinearMap.comp (switchMap R M N) := sorry
-- Proof strategy: use tensor-product induction and determinant-map extensionality; expand both
-- `splitIso_spec` formulas, transport exterior generators along `LinearEquiv.prodComm`, commute the
-- two exterior blocks, and identify the Koszul scalar with `projectiveDet (-LinearMap.id)` using
-- the projective determinant comparison with the finite-free case.

/-- Pointwise form of `commutes`, convenient for tensor generators. -/
@[stacks 0FJE "pointwise split determinant symmetry"]
theorem commutes_apply (x : det[R](M) ⊗[R] det[R](N)) :
    Module.Determinant.mapIso (LinearEquiv.prodComm R M N)
        (splitIso R M N x) =
      splitIso R N M (switchMap R M N x) := sorry
-- Proof strategy: apply `LinearMap.congr_fun commutes` to `x` and unfold linear-map composition.

end Module.Determinant.Split

end
