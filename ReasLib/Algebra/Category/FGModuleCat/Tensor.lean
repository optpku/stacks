/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import ReasLib.CategoryTheory.Linear.Functor

/-!
# Tensor comparison for module-linear functors

Left tensoring restricts to finitely generated modules. A module-linear functor
has a canonical comparison from tensoring with its value on the base field.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace FGModuleCat

variable {K : Type u} [Field K]

/-- The functor `V ↦ M ⊗[K] V` from finitely generated `K`-modules to all
`K`-modules. -/
def tensoringLeft (M : ModuleCat.{u} K) : FGModuleCat.{u} K ⥤ ModuleCat.{u} K :=
  forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K) ⋙ MonoidalCategory.tensorLeft M

/-- `tensoringLeft M` sends `V` to `M ⊗[K] V`. -/
theorem tensoringLeft_obj (M : ModuleCat.{u} K) (V : FGModuleCat.{u} K) :
    (tensoringLeft M).obj V = ModuleCat.of K (M ⊗[K] V) := rfl

/-- `tensoringLeft M` acts on morphisms by `id ⊗ f`. -/
theorem tensoringLeft_map {M : ModuleCat.{u} K} {V W : FGModuleCat.{u} K} (f : V ⟶ W) :
    (tensoringLeft M).map f =
      ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom.hom) := rfl

/-- Left tensoring by a fixed `K`-module is a `K`-linear functor on
`FGModuleCat K`. -/
instance instModuleLinear_tensoringLeft (M : ModuleCat.{u} K) :
    (tensoringLeft M).ModuleLinear K := by
  dsimp only [tensoringLeft]
  exact { toAdditive := inferInstance, toLinear := inferInstance }

/-- The `K`-linear map `f_v : K ⟶ V` sending `1` to `v`. -/
def spanSingleton {V : FGModuleCat.{u} K} (v : V) : of K K ⟶ V :=
  ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.toSpanSingleton K V v))

/-- `spanSingleton v` sends `1` to `v`. -/
theorem spanSingleton_apply_one {V : FGModuleCat.{u} K} (v : V) :
    (spanSingleton v).hom (1 : K) = v :=
  LinearMap.toSpanSingleton_apply_one K V v

/-- The bilinear map `(x, v) ↦ L.map (spanSingleton v) x`. -/
def tensorBilin (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K]
    (V : FGModuleCat.{u} K) :
    L.obj (of K K) →ₗ[K] V →ₗ[K] L.obj V :=
  LinearMap.mk₂ K (fun x v ↦ L.map (spanSingleton v) x)
    (fun x y v ↦ (L.map (spanSingleton v)).hom.map_add x y)
    (fun scalar x v ↦ (L.map (spanSingleton v)).hom.map_smul scalar x)
    (by
      intro x v w
      have span_add : spanSingleton (v + w) = spanSingleton v + spanSingleton w := by
        apply FGModuleCat.hom_ext
        exact LinearMap.toSpanSingleton_add v w
      rw [span_add, L.map_add]
      rfl)
    (by
      intro scalar x v
      have span_smul : spanSingleton (scalar • v) = scalar • spanSingleton v := by
        apply FGModuleCat.hom_ext
        exact LinearMap.toSpanSingleton_smul scalar v
      rw [span_smul, L.map_smul]
      rfl)

/-- The canonical comparison `tensoringLeft (L.obj (of K K)) ⟶ L`, given on
pure tensors by `x ⊗ₜ v ↦ L.map (spanSingleton v) x`. -/
def tensorNatTrans (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    tensoringLeft (L.obj (of K K)) ⟶ L where
  app V := ModuleCat.ofHom (TensorProduct.lift (tensorBilin L V))
  naturality := by
    intro V W f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x v
    change L.map (spanSingleton (f.hom v)) x = L.map f (L.map (spanSingleton v) x)
    have h : spanSingleton (f.hom v) = spanSingleton v ≫ f := by
      apply FGModuleCat.hom_ext
      exact (LinearMap.comp_toSpanSingleton f.hom.hom v).symm
    rw [h, L.map_comp]
    rfl

/-- The component of `tensorNatTrans L` at `V` is the lift of `tensorBilin L V`. -/
theorem tensorNatTrans_app (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K]
    (V : FGModuleCat.{u} K) :
    (tensorNatTrans L).app V = ModuleCat.ofHom (TensorProduct.lift (tensorBilin L V)) := rfl

/-- On pure tensors, `tensorNatTrans L` is `x ⊗ₜ v ↦ L.map (spanSingleton v) x`. -/
theorem tensorNatTrans_app_tmul (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K]
    {V : FGModuleCat.{u} K} (x : L.obj (of K K)) (v : V) :
    (tensorNatTrans L).app V (x ⊗ₜ v) = L.map (spanSingleton v) x := rfl

/-- At `V = K`, the comparison is right multiplication `L(K) ⊗[K] K → L(K)`. -/
theorem tensorNatTrans_app_of (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    (tensorNatTrans L).app (of K K) =
      ModuleCat.ofHom (TensorProduct.rid K (L.obj (of K K))).toLinearMap := by
  apply ModuleCat.hom_ext
  refine TensorProduct.ext' (fun x (v : K) => ?_)
  change L.map (spanSingleton v) x = (TensorProduct.rid K (L.obj (of K K))) (x ⊗ₜ v)
  rw [TensorProduct.rid_tmul]
  have h : spanSingleton (V := of K K) (v : K) = (v : K) • 𝟙 (of K K) := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r * v = v * r
    exact mul_comm r v
  rw [h, L.map_smul, L.map_id]
  rfl

/-- Every `K`-linear functor from finitely generated `K`-modules to all
`K`-modules is naturally isomorphic, via the canonical tensor comparison, to
left tensoring by its value on `K`. -/
instance isIso_tensorNatTrans (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    IsIso (tensorNatTrans L) := by
  classical
  have happ (V : FGModuleCat.{u} K) : IsIso ((tensorNatTrans L).app V) := by
    let b := Module.Basis.ofVectorSpace K V
    let p (i : Module.Basis.ofVectorSpaceIndex K V) : V ⟶ of K K :=
      ObjectProperty.homMk (ModuleCat.ofHom (b.coord i))
    let q : L.obj V →ₗ[K] L.obj (of K K) ⊗[K] V :=
      ∑ i, ((TensorProduct.mk K (L.obj (of K K)) V).flip (b i)).comp (L.map (p i)).hom
    have hq (y : L.obj V) : q y = ∑ i, L.map (p i) y ⊗ₜ[K] b i := by
      simp [q]
    have hp (i : Module.Basis.ofVectorSpaceIndex K V) (v : V) :
        spanSingleton v ≫ p i = (b.coord i v) • 𝟙 (of K K) := by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro r
      change b.coord i (r • v) = (b.coord i v) * r
      rw [map_smul, smul_eq_mul, mul_comm]
    have hid : ∑ i, p i ≫ spanSingleton (b i) = 𝟙 V := by
      apply (forget₂ (FGModuleCat.{u} K) (ModuleCat.{u} K)).map_injective
      rw [Functor.map_sum]
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_sum]
      apply LinearMap.ext
      intro v
      rw [LinearMap.sum_apply]
      change (∑ i, b.coord i v • b i) = v
      exact b.sum_repr v
    refine ⟨⟨ModuleCat.ofHom q, ?_, ?_⟩⟩
    · apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x v
      change q ((tensorNatTrans L).app V (x ⊗ₜ v)) = x ⊗ₜ v
      rw [tensorNatTrans_app_tmul, hq]
      have heval (i : Module.Basis.ofVectorSpaceIndex K V) :
          L.map (p i) (L.map (spanSingleton v) x) = (b.coord i v) • x := by
        change (L.map (spanSingleton v) ≫ L.map (p i)) x = _
        rw [← L.map_comp, hp, L.map_smul, L.map_id]
        rfl
      simp_rw [heval, TensorProduct.smul_tmul]
      rw [← TensorProduct.tmul_sum]
      exact congrArg (fun w : V => x ⊗ₜ[K] w) (b.sum_repr v)
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change (TensorProduct.lift (tensorBilin L V)) (q y) = y
      rw [hq, map_sum]
      simp only [TensorProduct.lift.tmul]
      change (∑ i, L.map (spanSingleton (b i)) (L.map (p i) y)) = y
      have hy : (∑ i, L.map (p i ≫ spanSingleton (b i))) = 𝟙 (L.obj V) := by
        rw [← L.map_sum, hid, L.map_id]
      simpa only [L.map_comp, ModuleCat.hom_sum, LinearMap.sum_apply,
        ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply]
        using congrArg (fun f : L.obj V ⟶ L.obj V => f.hom y) hy
  letI : ∀ V : FGModuleCat.{u} K, IsIso ((tensorNatTrans L).app V) := happ
  exact NatIso.isIso_of_isIso_app (tensorNatTrans L)

end FGModuleCat
