/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Diagonal group-ring action on a mixed tensor

This module equips a mixed tensor product with the diagonal group-ring action
and records its finite and projective module instances.
-/

@[expose] public section

noncomputable section

universe u v w p m

open scoped MonoidAlgebra TensorProduct

namespace TensorProduct

variable (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
variable [AddCommGroup P] [Module A P]
variable [AddCommGroup M] [Module A M]

/-- The tensor product `P ⊗[A] M`, as a type synonym for a diagonal module. -/
@[nolint unusedArguments]
def Diagonal (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
    [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
    [AddCommGroup P] [Module A P] [AddCommGroup M] [Module A M] : Type (max p m) :=
  P ⊗[A] M

namespace Diagonal

/-- The additive group structure inherited by the diagonal tensor. -/
instance instAddCommGroup : AddCommGroup (Diagonal A Λ G P M) :=
  inferInstanceAs (AddCommGroup (P ⊗[A] M))

/-- The left `A`-module structure inherited by the diagonal tensor. -/
instance instModuleA : Module A (Diagonal A Λ G P M) :=
  inferInstanceAs (Module A (P ⊗[A] M))

/-- An elementary tensor viewed in the diagonal type synonym. -/
def tmul (p : P) (m : M) : Diagonal A Λ G P M := p ⊗ₜ[A] m

/-- The canonical additive equivalence from the diagonal synonym to the raw tensor. -/
def addEquiv : Diagonal A Λ G P M ≃+ P ⊗[A] M :=
  AddEquiv.refl _

/-- The additive equivalence sends elementary tensors to elementary tensors. -/
theorem addEquiv_tmul (p : P) (m : M) :
    addEquiv A Λ G P M (tmul A Λ G P M p m) = p ⊗ₜ[A] m := by
  rfl

end Diagonal

variable [Module Λ M] [IsScalarTower A Λ M]

set_option backward.privateInPublic true in
/-- The unit law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_one :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (1 : Λ)) =
      (1 : Module.End A (Diagonal A Λ G P M)) := by
  have h : DistribSMul.toLinearMap A M (1 : Λ) = LinearMap.id := by
    ext m
    simp [DistribSMul.toLinearMap]
  rw [h, TensorProduct.map_id]
  rfl

set_option backward.privateInPublic true in
/-- The multiplicative law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_mul (r s : Λ) :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (r * s)) =
      map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M r) *
        map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M s) := by
  apply TensorProduct.ext'
  intro p m
  simp [mul_smul]

set_option backward.privateInPublic true in
/-- The zero law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_zero :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (0 : Λ)) =
      (0 : Module.End A (Diagonal A Λ G P M)) := by
  have h : DistribSMul.toLinearMap A M (0 : Λ) = 0 := by
    ext m
    simp [DistribSMul.toLinearMap]
  rw [h, TensorProduct.map_zero_right]
  rfl

set_option backward.privateInPublic true in
/-- The additive law for the second-factor scalar endomorphisms. -/
private theorem lsmulRight_map_add (r s : Λ) :
    map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M (r + s)) =
      map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M r) +
        map (LinearMap.id : P →ₗ[A] P) (DistribSMul.toLinearMap A M s) := by
  have h : DistribSMul.toLinearMap A M (r + s) =
      DistribSMul.toLinearMap A M r + DistribSMul.toLinearMap A M s := by
    ext m
    simp [DistribSMul.toLinearMap, add_smul]
  rw [h, TensorProduct.map_add_right]

set_option backward.privateInPublic true in
/-- Left `Λ`-scaling on the second factor, as `A`-endomorphisms of the tensor. -/
def lsmulRight : Λ →+* Module.End A (Diagonal A Λ G P M) where
  toFun r := map LinearMap.id (DistribSMul.toLinearMap A M r)
  map_one' := lsmulRight_map_one A Λ G P M
  map_mul' := fun r s =>
    lsmulRight_map_mul (A := A) (Λ := Λ) (P := P) (M := M) r s
  map_zero' := lsmulRight_map_zero A Λ G P M
  map_add' := fun r s =>
    lsmulRight_map_add (A := A) (Λ := Λ) (P := P) (M := M) r s

/-- Left `Λ`-scaling acts on elementary tensors through the second factor. -/
theorem lsmulRight_tmul (r : Λ) (p : P) (m : M) :
    lsmulRight A Λ G P M r (Diagonal.tmul A Λ G P M p m) =
      Diagonal.tmul A Λ G P M p (r • m) := by
  change TensorProduct.map (LinearMap.id : P →ₗ[A] P)
      (DistribSMul.toLinearMap A M r) (p ⊗ₜ[A] m) = p ⊗ₜ[A] (r • m)
  rw [TensorProduct.map_tmul]
  rfl

variable [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]

/-- The `A`-action on `M` is the restriction of the `Λ[G]`-action. -/
instance instIsScalarTower : IsScalarTower A (Λ[G]) M :=
  IsScalarTower.to₁₃₄ A Λ (Λ[G]) M

set_option backward.privateInPublic true in
/-- The unit law for the diagonal group endomorphisms. -/
private theorem diagonalOf_map_one :
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G 1))
        (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G 1)) =
      (1 : Module.End A (Diagonal A Λ G P M)) := by
  have hP : DistribSMul.toLinearMap A P (MonoidAlgebra.of A G 1) = LinearMap.id := by
    ext p
    change MonoidAlgebra.of A G (1 : G) • p = p
    simpa only [map_one, one_smul]
  have hM : DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G 1) = LinearMap.id := by
    ext m
    change MonoidAlgebra.of Λ G (1 : G) • m = m
    simpa only [map_one, one_smul]
  rw [hP, hM, TensorProduct.map_id]
  rfl

set_option backward.privateInPublic true in
/-- The multiplicative law for the diagonal group endomorphisms. -/
private theorem diagonalOf_map_mul (g h : G) :
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G (g * h)))
        (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G (g * h))) =
      map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g))
          (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g)) *
        map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G h))
          (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G h)) := by
  have hP : DistribSMul.toLinearMap A P (MonoidAlgebra.of A G (g * h)) =
      DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g) *
        DistribSMul.toLinearMap A P (MonoidAlgebra.of A G h) := by
    ext p
    change MonoidAlgebra.of A G (g * h) • p =
      MonoidAlgebra.of A G g • (MonoidAlgebra.of A G h • p)
    simpa only [map_mul, mul_smul]
  have hM : DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G (g * h)) =
      DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g) *
        DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G h) := by
    ext m
    change MonoidAlgebra.of Λ G (g * h) • m =
      MonoidAlgebra.of Λ G g • (MonoidAlgebra.of Λ G h • m)
    simpa only [map_mul, mul_smul]
  rw [hP, hM, TensorProduct.map_mul]

set_option backward.privateInPublic true in
/-- The diagonal `G`-action on the tensor, as `A`-endomorphisms. -/
def diagonalOf : G →* Module.End A (Diagonal A Λ G P M) where
  toFun g :=
    map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g))
      (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g))
  map_one' := diagonalOf_map_one A Λ G P M
  map_mul' := diagonalOf_map_mul A Λ G P M

/-- The diagonal group action sends elementary tensors to elementary tensors. -/
theorem diagonalOf_tmul (g : G) (p : P) (m : M) :
    diagonalOf A Λ G P M g (Diagonal.tmul A Λ G P M p m) =
      Diagonal.tmul A Λ G P M (MonoidAlgebra.of A G g • p)
        (MonoidAlgebra.of Λ G g • m) := by
  change TensorProduct.map (DistribSMul.toLinearMap A P (MonoidAlgebra.of A G g))
      (DistribSMul.toLinearMap A M (MonoidAlgebra.of Λ G g))
      (p ⊗ₜ[A] m) = _
  rw [TensorProduct.map_tmul]
  rfl

set_option backward.privateInPublic true in
/-- The group-ring homomorphism encoding the diagonal `Λ[G]`-action. -/
private theorem lsmulRight_commute_diagonalOf (r : Λ) (g : G) :
    Commute (lsmulRight A Λ G P M r) (diagonalOf A Λ G P M g) := by
  apply TensorProduct.ext'
  intro p m
  change Diagonal.tmul A Λ G P M (MonoidAlgebra.of A G g • p)
      (r • (MonoidAlgebra.of Λ G g • m)) =
    Diagonal.tmul A Λ G P M (MonoidAlgebra.of A G g • p)
      (MonoidAlgebra.of Λ G g • (r • m))
  rw [show MonoidAlgebra.of Λ G g • (r • m) =
      r • (MonoidAlgebra.of Λ G g • m) by
    rw [← smul_one_smul (Λ[G]) r m, ← mul_smul, ← smul_assoc]
    congr 1
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.one_def,
      MonoidAlgebra.single_mul_single, MonoidAlgebra.smul_single]]

set_option backward.privateInPublic true in
/-- The group-ring map encoding the diagonal `Λ[G]`-action on the tensor. -/
def liftDiagonal : Λ[G] →+* Module.End A (Diagonal A Λ G P M) :=
  MonoidAlgebra.liftNCRingHom (lsmulRight A Λ G P M) (diagonalOf A Λ G P M)
    (lsmulRight_commute_diagonalOf A Λ G P M)

/-- On basis elements, the diagonal action is scalar multiplication after the group action. -/
theorem liftDiagonal_single (g : G) (r : Λ) :
    liftDiagonal A Λ G P M (MonoidAlgebra.single g r) =
      lsmulRight A Λ G P M r * diagonalOf A Λ G P M g := by
  exact MonoidAlgebra.liftNCRingHom_single _ _ _ g r

namespace Diagonal

/-- The diagonal left `Λ[G]`-module structure on the tensor. -/
instance instModule : Module (Λ[G]) (Diagonal A Λ G P M) :=
  Module.compHom (Diagonal A Λ G P M) (liftDiagonal A Λ G P M)

/-- The diagonal action on elementary tensors for an arbitrary group-ring element. -/
theorem smul_tmul (x : Λ[G]) (p : P) (m : M) :
    x • tmul A Λ G P M p m =
      x.coeff.sum fun g r ↦
        tmul A Λ G P M (MonoidAlgebra.of A G g • p)
          (r • (MonoidAlgebra.of Λ G g • m)) := by
  classical
  conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
  simp only [Finsupp.sum, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro g hg
  change liftDiagonal A Λ G P M (MonoidAlgebra.single g (x.coeff g))
      (tmul A Λ G P M p m) = _
  rw [liftDiagonal_single, Module.End.mul_apply, diagonalOf_tmul, lsmulRight_tmul]

/-- A group element acts diagonally on elementary tensors. -/
theorem smul_of (g : G) (p : P) (m : M) :
    MonoidAlgebra.of Λ G g • tmul A Λ G P M p m =
      tmul A Λ G P M (MonoidAlgebra.of A G g • p) (MonoidAlgebra.of Λ G g • m) := by
  change liftDiagonal A Λ G P M (MonoidAlgebra.of Λ G g)
      (tmul A Λ G P M p m) = _
  rw [MonoidAlgebra.of_apply, liftDiagonal_single, Module.End.mul_apply,
    diagonalOf_tmul, lsmulRight_tmul]
  simp [MonoidAlgebra.of_apply]

/-- A basis element `r · g` acts diagonally on elementary tensors. -/
theorem smul_single (g : G) (r : Λ) (p : P) (m : M) :
    MonoidAlgebra.single g r • tmul A Λ G P M p m =
      tmul A Λ G P M (MonoidAlgebra.of A G g • p)
        (r • (MonoidAlgebra.of Λ G g • m)) := by
  change liftDiagonal A Λ G P M (MonoidAlgebra.single g r)
      (tmul A Λ G P M p m) = _
  rw [liftDiagonal_single, Module.End.mul_apply, diagonalOf_tmul, lsmulRight_tmul]

/-- The diagonal tensor is finite when `P` and `M` have the stated finiteness. -/
instance instFinite [Module.Finite (A[G]) P] [Module.Finite Λ M] :
    Module.Finite (Λ[G]) (Diagonal A Λ G P M) := by
  classical
  obtain ⟨nP, s, hs⟩ := Module.Finite.exists_fin (R := A[G]) (M := P)
  obtain ⟨nM, t, ht⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  let S : Submodule (Λ[G]) (Diagonal A Λ G P M) :=
    Submodule.span (Λ[G]) (Set.range fun ij : Fin nP × Fin nM ↦
      tmul A Λ G P M (s ij.1) (t ij.2))
  have hzero (p : P) : tmul A Λ G P M p 0 = 0 :=
    TensorProduct.tmul_zero M p
  have hzero' (m : M) : tmul A Λ G P M 0 m = 0 :=
    TensorProduct.zero_tmul P m
  have hadd (p : P) (m m' : M) : tmul A Λ G P M p (m + m') =
      tmul A Λ G P M p m + tmul A Λ G P M p m' :=
    TensorProduct.tmul_add p m m'
  have hadd' (p p' : P) (m : M) : tmul A Λ G P M (p + p') m =
      tmul A Λ G P M p m + tmul A Λ G P M p' m :=
    TensorProduct.add_tmul p p' m
  have hcoeff (p : P) (m : M) (r : Λ) :
      tmul A Λ G P M p (r • m) =
        MonoidAlgebra.single (1 : G) r • tmul A Λ G P M p m := by
    rw [smul_single]
    simp only [map_one, one_smul]
  -- Move a group element from the first factor to its inverse on the second.
  have hleft (g : G) (a : A) (p : P) (m : M) :
      tmul A Λ G P M (MonoidAlgebra.single g a • p) m =
        MonoidAlgebra.single g (algebraMap A Λ a) •
          tmul A Λ G P M p (MonoidAlgebra.of Λ G g⁻¹ • m) := by
    rw [smul_single]
    have hinv : MonoidAlgebra.of Λ G g •
        (MonoidAlgebra.of Λ G g⁻¹ • m) = m := by
      rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    rw [hinv]
    change (MonoidAlgebra.single g a • p) ⊗ₜ[A] m =
      (MonoidAlgebra.of A G g • p) ⊗ₜ[A] ((algebraMap A Λ a) • m)
    simp only [MonoidAlgebra.single_eq_algebraMap_mul_of, mul_smul,
      IsScalarTower.algebraMap_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  have hgen (i : Fin nP) (m : M) : tmul A Λ G P M (s i) m ∈ S := by
    have hm : m ∈ Submodule.span Λ (Set.range t) := by
      rw [ht]
      trivial
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact Submodule.subset_span ⟨(i, j), rfl⟩
    | zero =>
      rw [hzero]
      exact S.zero_mem
    | add x y hx hy ihx ihy =>
      rw [hadd]
      exact S.add_mem ihx ihy
    | smul r x hx ih =>
      rw [hcoeff]
      exact S.smul_mem _ ih
  have hall (p : P) : ∀ m : M, tmul A Λ G P M p m ∈ S := by
    have hp : p ∈ Submodule.span (A[G]) (Set.range s) := by
      rw [hs]
      trivial
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hgen i
    | zero =>
      intro m
      rw [hzero']
      exact S.zero_mem
    | add x y hx hy ihx ihy =>
      intro m
      rw [hadd']
      exact S.add_mem (ihx m) (ihy m)
    | smul r x hx ih =>
      intro m
      induction r using MonoidAlgebra.induction_linear with
      | zero =>
        rw [zero_smul, hzero']
        exact S.zero_mem
      | add r q ihr ihq =>
        rw [add_smul, hadd']
        exact S.add_mem ihr ihq
      | single g a =>
        rw [hleft]
        exact S.smul_mem _ (ih _)
  have hS : S = ⊤ := by
    apply top_unique
    intro z _
    exact TensorProduct.induction_on z S.zero_mem hall
      (fun z z' hz hz' ↦ S.add_mem hz hz')
  apply Module.Finite.of_fg_top
  rw [Submodule.fg_def]
  exact ⟨_, Set.finite_range _, hS⟩

/-- The diagonal tensor is projective when `P` and `M` have the stated projectivity. -/
instance instProjective [Module.Projective (A[G]) P] [Module.Projective Λ M] :
    Module.Projective (Λ[G]) (Diagonal A Λ G P M) := sorry

end Diagonal

end TensorProduct
