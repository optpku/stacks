/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Eventual

/-!
# Kernels and cokernels of morphisms of ℤ_[ℓ]-sheaves

The cokernel of a morphism of `ℤ_[ℓ]`-sheaves is the inverse system of stagewise cokernels.
The kernel is obtained by applying `ofEventuallyConstant` to the stable-image system of
naive kernels, whose stage `n` is the kernel of the map from the naive kernel into the
product of cokernels of later transitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf CategoryTheory.SequentialInverseSystem
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The naive inverse system of stagewise kernels of a morphism of `ℤ_[ℓ]`-sheaves. -/
abbrev naiveKerSystem {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  kernel (hom α)

/-- Stage `n` of the naive kernel system is the kernel of the stage-`n` component. -/
def naiveKerSystem_objIso {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (naiveKerSystem α).family n ≅ kernel (hom_app α n) :=
  PreservesKernel.iso
    ((CategoryTheory.evaluation ℕᵒᵖ (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})).obj (op n)) (hom α)

/-- The map from naive kernel stage `n` to the product of cokernels of all later
transitions. Its kernel is the stable image at stage `n`. -/
def stableImageToCokernelProduct {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (naiveKerSystem α).family n ⟶
      ∏ᶜ fun k : ℕ ↦ cokernel ((naiveKerSystem α).transitionMap (Nat.le_add_left n k)) :=
  Pi.lift fun k ↦
    cokernel.π ((naiveKerSystem α).transitionMap (Nat.le_add_left n k))

/-- Stage `n` of the stable-image tower, i.e. the intersection of images of
transitions from later naive kernel stages. -/
def stableImageStage {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  kernel (stableImageToCokernelProduct α n)

/-- The naive-kernel successor maps the stable image at stage `n + 1` into the
kernel of the stage-`n` cokernel-product comparison. -/
theorem stableImageStepMap_comp_eq_zero {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (kernel.ι (stableImageToCokernelProduct α (n + 1)) ≫ (naiveKerSystem α).stepMap n) ≫
      stableImageToCokernelProduct α n = 0 := sorry

/-- Successor maps of the stable-image tower, induced by naive-kernel transitions. -/
def stableImageStepMap {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    stableImageStage α (n + 1) ⟶ stableImageStage α n :=
  kernel.lift (stableImageToCokernelProduct α n)
    (kernel.ι (stableImageToCokernelProduct α (n + 1)) ≫ (naiveKerSystem α).stepMap n)
    (stableImageStepMap_comp_eq_zero α n)

/-- The stable-image inverse system `{∩_{m ≥ n} Im(Ker φ_m → Ker φ_n)}`. -/
def stableImageSystem {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.ofOpSequence (stableImageStepMap α)

/-- Stage `n` of `stableImageSystem` is the named stable-image object. -/
theorem stableImageSystem_obj {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (stableImageSystem α).family n = stableImageStage α n := sorry

/-- Successor maps of `stableImageSystem` are the named stable-image step maps. -/
theorem stableImageSystem_stepMap {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (stableImageSystem α).stepMap n = stableImageStepMap α n := sorry

/-- Each stable-image stage is annihilated by `ℓ^{n+1}`. -/
theorem stableImageSystem_isKilled {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    ∀ n, (ℓ ^ (n + 1)) • 𝟙 ((stableImageSystem α).family n) = 0 := sorry

/-- Each stable-image stage is constructible as an étale sheaf of `ZMod`-modules. -/
theorem stableImageSystem_isConstructible {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    ∀ n, IsConstructibleEtale
      (fun {Y : Scheme.{u}} (f : Y ⟶ X) ↦
        ((smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y : Scheme.{u}} (H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) ↦
        IsFiniteLocallyConstantAddCommGrp H) ((stableImageSystem α).family n) := sorry

/-- Every nsmul reduction of the stable-image system is eventually constant. -/
theorem stableImageSystem_isEventuallyConstantModNsmul {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    (stableImageSystem α).IsEventuallyConstantModNsmul ℓ := sorry

/-- The kernel of a morphism of `ℤ_[ℓ]`-sheaves, obtained by applying
`ofEventuallyConstant` to the stable-image system of naive kernels. -/
def ker {F G : ZEllSheaf X ℓ} (α : Hom F G) : ZEllSheaf X ℓ :=
  ofEventuallyConstant (stableImageSystem α) (stableImageSystem_isKilled α)
    (stableImageSystem_isConstructible α)
    (stableImageSystem_isEventuallyConstantModNsmul α)

/-- Stage `n` of `ker α` is the inverse limit of the `ℓ^{n+1}`-reductions of the
stable-image system. -/
theorem ker_stage {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (ker α).stage n = limit ((stableImageSystem α).modNsmulSystem ℓ n) := sorry

/-- `ker α` is `ofEventuallyConstant` applied to the stable-image kernel system. -/
theorem ker_spec {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    ker α =
      ofEventuallyConstant (stableImageSystem α) (stableImageSystem_isKilled α)
        (stableImageSystem_isConstructible α)
        (stableImageSystem_isEventuallyConstantModNsmul α) := sorry

/-- Inclusion of a stable-image stage into the corresponding stage of the domain. -/
def stableImageInclusion {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (stableImageSystem α).family n ⟶ F.stage n :=
  kernel.ι (stableImageToCokernelProduct α n) ≫ (kernel.ι (hom α)).app (op n)

/-- Multiplication by `ℓ^{n+1}` vanishes after the stable-image inclusion into `F`. -/
theorem stableImageInclusion_nsmul {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    ((ℓ ^ (n + 1)) • 𝟙 ((stableImageSystem α).family n)) ≫ stableImageInclusion α n = 0 :=
  sorry

/-- The comparison from the stage-`n` nsmul cokernel of the stable-image system to `F`. -/
def stableImageModNsmulToStage {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    nsmulCokernel ((stableImageSystem α).family n) (ℓ ^ (n + 1)) ⟶ F.stage n :=
  cokernel.desc ((ℓ ^ (n + 1)) • 𝟙 ((stableImageSystem α).family n))
    (stableImageInclusion α n) (stableImageInclusion_nsmul α n)

/-- Stage components of the kernel inclusion, via the eventual-system projections. -/
def kerι_app {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (ker α).stage n ⟶ F.stage n :=
  limit.π ((stableImageSystem α).modNsmulSystem ℓ n) (op n) ≫
    stableImageModNsmulToStage α n

/-- Kernel-inclusion components are natural with respect to successor transitions. -/
theorem kerι_naturality {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (ker α).system.map (homOfLE (n.le_add_right 1)).op ≫ kerι_app α n =
      kerι_app α (n + 1) ≫ F.system.map (homOfLE (n.le_add_right 1)).op := sorry

/-- The kernel inclusion `ker α ⟶ F`. -/
def kerι {F G : ZEllSheaf X ℓ} (α : Hom F G) : Hom (ker α) F :=
  homMk (NatTrans.ofOpSequence (kerι_app α) (kerι_naturality α))

/-- Stage components of `kerι` are the named eventual-system comparisons. -/
theorem kerι_app_eq {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    hom_app (kerι α) n = kerι_app α n := sorry

/-- The kernel inclusion composes to zero with `α`. -/
theorem ker_condition {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    kerι α ≫ α = 0 := sorry

/-- The system laws hold for the stagewise cokernel system of a morphism of
`ℤ_[ℓ]`-sheaves. -/
instance instIsZEllSheafSystemCoker {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    IsZEllSheafSystem X ℓ (cokernel (hom α)) := sorry

/-- The cokernel of a morphism of `ℤ_[ℓ]`-sheaves is the inverse system of
stagewise cokernels. -/
def coker {F G : ZEllSheaf X ℓ} (α : Hom F G) : ZEllSheaf X ℓ :=
  ofSystem (cokernel (hom α))
    (instIsZEllSheafSystemCoker α).isKilled
    (instIsZEllSheafSystemCoker α).step_comp_nsmul
    (instIsZEllSheafSystemCoker α).isAdic
    (instIsZEllSheafSystemCoker α).isConstructible

/-- Stage `n` of `coker α` is the cokernel of the stage-`n` component. -/
def coker_stageIso {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    (coker α).stage n ≅ cokernel (hom_app α n) :=
  PreservesCokernel.iso
    ((CategoryTheory.evaluation ℕᵒᵖ (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})).obj (op n)) (hom α)

/-- The cokernel system is the functor-category cokernel of the underlying morphism. -/
theorem coker_spec {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    (coker α).system = cokernel (hom α) := sorry

/-- The cokernel projection `G ⟶ coker α`. -/
def cokerπ {F G : ZEllSheaf X ℓ} (α : Hom F G) : Hom G (coker α) :=
  homMk (cokernel.π (hom α))

/-- Stage components of `cokerπ` are the stagewise cokernel projections. -/
theorem cokerπ_app {F G : ZEllSheaf X ℓ} (α : Hom F G) (n : ℕ) :
    hom_app (cokerπ α) n = cokernel.π (hom_app α n) ≫ (coker_stageIso α n).inv := sorry

/-- The cokernel projection composes to zero with `α`. -/
theorem coker_condition {F G : ZEllSheaf X ℓ} (α : Hom F G) :
    α ≫ cokerπ α = 0 := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
