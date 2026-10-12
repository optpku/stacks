/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import stacks_project.Chap90.Definition_90_11_1_ModuleLinear

/-!
# Tensoring finitely generated modules on the left

Restriction of `M ⊗[K] -` from `FGModuleCat K` to `ModuleCat K`, together with
the canonical comparison of a `K`-linear functor against tensoring by its value
on `K`.
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
def tensoringLeft (M : ModuleCat.{u} K) : FGModuleCat.{u} K ⥤ ModuleCat.{u} K where
  obj V := ModuleCat.of K (M ⊗[K] V)
  map f := ModuleCat.ofHom (TensorProduct.map LinearMap.id f.hom.hom)
  map_id := sorry
  map_comp := sorry

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
  LinearMap.mk₂ K (fun x v ↦ L.map (spanSingleton v) x) sorry sorry sorry sorry

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

end FGModuleCat
