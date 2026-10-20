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
    (tensoringLeft M).obj V = ModuleCat.of K (M ⊗[K] V) := sorry

/-- `tensoringLeft M` acts on morphisms by `id ⊗ f`. -/
theorem tensoringLeft_map {M : ModuleCat.{u} K} {V W : FGModuleCat.{u} K} (f : V ⟶ W) :
    (tensoringLeft M).map f =
      ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom.hom) := sorry

/-- Left tensoring by a fixed `K`-module is a `K`-linear functor on
`FGModuleCat K`. -/
instance instModuleLinear_tensoringLeft (M : ModuleCat.{u} K) :
    (tensoringLeft M).ModuleLinear K := sorry

/-- The `K`-linear map `f_v : K ⟶ V` sending `1` to `v`. -/
def spanSingleton {V : FGModuleCat.{u} K} (v : V) : of K K ⟶ V :=
  ObjectProperty.homMk (ConcreteCategory.ofHom (LinearMap.toSpanSingleton K V v))

/-- `spanSingleton v` sends `1` to `v`. -/
theorem spanSingleton_apply_one {V : FGModuleCat.{u} K} (v : V) :
    (spanSingleton v).hom (1 : K) = v := sorry

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
  naturality := sorry

/-- The component of `tensorNatTrans L` at `V` is the lift of `tensorBilin L V`. -/
theorem tensorNatTrans_app (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K]
    (V : FGModuleCat.{u} K) :
    (tensorNatTrans L).app V = ModuleCat.ofHom (TensorProduct.lift (tensorBilin L V)) := sorry

/-- On pure tensors, `tensorNatTrans L` is `x ⊗ₜ v ↦ L.map (spanSingleton v) x`. -/
theorem tensorNatTrans_app_tmul (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K]
    {V : FGModuleCat.{u} K} (x : L.obj (of K K)) (v : V) :
    (tensorNatTrans L).app V (x ⊗ₜ v) = L.map (spanSingleton v) x := sorry

/-- At `V = K`, the comparison is right multiplication `L(K) ⊗[K] K → L(K)`. -/
theorem tensorNatTrans_app_of (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    (tensorNatTrans L).app (of K K) =
      ModuleCat.ofHom (TensorProduct.rid K (L.obj (of K K))).toLinearMap := sorry

/-- Every `K`-linear functor from finitely generated `K`-modules to all
`K`-modules is naturally isomorphic, via the canonical tensor comparison, to
left tensoring by its value on `K`. -/
instance isIso_tensorNatTrans (L : FGModuleCat.{u} K ⥤ ModuleCat.{u} K) [L.ModuleLinear K] :
    IsIso (tensorNatTrans L) := sorry

end FGModuleCat
