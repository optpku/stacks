/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Differentials.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Conormal
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Conormal sequences on a ringed site

This module constructs the conormal sequence of composable morphisms of commutative-ring
sheaves on an arbitrary site.  It exposes both the objectwise formula
`I / I ^ 2 ⟶ O₃ ⊗[O₂] Ω(O₂/O₁)` and the sheaf-level short exact sequence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open PresheafOfModules.DifferentialsConstruction
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe c v w

namespace SheafOfModules.RingedSite

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O₁ O₂ O₃ : Sheaf J CommRingCat.{w}}

/-- The kernel ideal of a ring-sheaf morphism on one object of the site. -/
abbrev conormalIdeal
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    Ideal (O₂.obj.obj U) :=
  PresheafOfModules.KernelCotangent.ideal α.hom U

section

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat.{w})]

/-- Kernel ideals of a ring-sheaf morphism are compatible with restriction. -/
theorem conormalIdeal_le_comap
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalIdeal α U ≤
      (conormalIdeal α V).comap ((O₂.obj.map i).hom) := sorry

end

/-- The objectwise cotangent module `I / I ^ 2`. -/
abbrev conormalObj
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    ModuleCat (O₂.obj.obj U) :=
  PresheafOfModules.KernelCotangent.obj α.hom U

/-- Restriction maps on the objectwise cotangent modules. -/
abbrev conormalRestriction
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    conormalObj α U ⟶
      (ModuleCat.restrictScalars
        (((ringSheaf J O₂).obj.map i).hom)).obj
        (conormalObj α V) :=
  PresheafOfModules.KernelCotangent.map α.hom i

/-- Restriction on conormal modules sends a cotangent generator to the restricted generator. -/
theorem conormalRestriction_toCotangent
    (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) (x : conormalIdeal α U) :
    conormalRestriction α i ((conormalIdeal α U).toCotangent x) =
      (conormalIdeal α V).toCotangent
        ⟨((O₂.obj.map i).hom) x, conormalIdeal_le_comap α i x.2⟩ := sorry

/-- Identity restrictions act trivially on the cotangent modules. -/
theorem conormalRestriction_id
    (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalRestriction α (𝟙 U) =
      (ModuleCat.restrictScalarsId'
        (((ringSheaf J O₂).obj.map (𝟙 U)).hom)
        (congrArg RingCat.Hom.hom
          ((ringSheaf J O₂).obj.map_id U))).inv.app _ := sorry

/-- Cotangent restriction maps compose functorially. -/
theorem conormalRestriction_comp
    (α : O₂ ⟶ O₃) {U V W : Cᵒᵖ} (i : U ⟶ V) (j : V ⟶ W) :
    conormalRestriction α (i ≫ j) =
      conormalRestriction α i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (conormalRestriction α j) ≫
        (ModuleCat.restrictScalarsComp'
          (((ringSheaf J O₂).obj.map i).hom)
          (((ringSheaf J O₂).obj.map j).hom)
          (((ringSheaf J O₂).obj.map (i ≫ j)).hom)
          (congrArg RingCat.Hom.hom
            ((ringSheaf J O₂).obj.map_comp i j))).inv.app _ := sorry

/-- The presheaf of objectwise conormal modules. -/
def conormalPresheaf
    (α : O₂ ⟶ O₃) :
    PresheafOfModules (ringSheaf J O₂).obj :=
  PresheafOfModules.KernelCotangent.presheaf α.hom

/-- The conormal sheaf before extension of scalars to the quotient ring sheaf. -/
noncomputable def conormalSourceOverSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₂) :=
  (PresheafOfModules.sheafification
      (𝟙 (ringSheaf J O₂).obj)).obj
    (conormalPresheaf α)

/-- The scalar-extended conormal source term. -/
@[stacks 08TF "conormal source", stacks 08TS "conormal source"]
abbrev conormalSource
    (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (extendAlong α).obj (conormalSourceOverSource α)

/-- The extension-restriction unit for the conormal source. -/
@[stacks 08TF "conormal extension unit", stacks 08TS "conormal extension unit"]
noncomputable def conormalSourceUnit
    (α : O₂ ⟶ O₃) :
    conormalSourceOverSource α ⟶
      (restrictionAlong α).obj (conormalSource α) :=
  (extendRestrictAdj α).unit.app (conormalSourceOverSource α)

/-- The canonical map from the conormal presheaf to the restricted scalar-extended sheaf. -/
@[stacks 08TS "conormal presheaf extension unit"]
noncomputable def conormalSourcePresheafUnit
    (α : O₂ ⟶ O₃) :
    conormalPresheaf α ⟶
      ((restrictionAlong α).obj (conormalSource α)).val :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).unit.app (conormalPresheaf α) ≫
    (conormalSourceUnit α).val

/-- The scalar-extended tensor term `O₃ ⊗[O₂] Ω(O₂/O₁)`. -/
@[stacks 08TF "base-changed differentials", stacks 08TS "conormal tensor term"]
abbrev conormalTensorTerm
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    SheafOfModules (ringSheaf J O₃) :=
  (extendAlong α).obj Ω(φ)

/-- The value `1 ⊗ d x` in the restricted scalar extension of relative differentials. -/
abbrev conormalGeneratorApply
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (x : conormalIdeal α U) :
    ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.obj U :=
  ((extendRestrictAdj α).unit.app Ω(φ)).val.app U
    (((relativeDifferential φ).app U).d x.1)

/-- The generator formula `x ↦ 1 ⊗ d x` is additive. -/
theorem conormalGeneratorApply_add
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (x y : conormalIdeal α U) :
    conormalGeneratorApply φ α U (x + y) =
      conormalGeneratorApply φ α U x + conormalGeneratorApply φ α U y := sorry

/-- The generator formula `x ↦ 1 ⊗ d x` is linear over the middle ring. -/
theorem conormalGeneratorApply_smul
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (r : O₂.obj.obj U) (x : conormalIdeal α U) :
    conormalGeneratorApply φ α U (r • x) =
      r • conormalGeneratorApply φ α U x := sorry

/-- The linear map on the kernel ideal sending `x` to `1 ⊗ d x`. -/
def conormalIdealToDifferentials
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalIdeal α U →ₗ[O₂.obj.obj U]
      ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.obj U where
  toFun := conormalGeneratorApply φ α U
  map_add' := conormalGeneratorApply_add φ α U
  map_smul' := conormalGeneratorApply_smul φ α U

/-- The generator map vanishes on products in the kernel ideal. -/
theorem conormalIdealToDifferentials_mul
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (x y : conormalIdeal α U) :
    conormalIdealToDifferentials φ α U (x * y) = 0 := sorry

/-- The sectionwise conormal map sends a class in `Ker(α) / Ker(α) ^ 2` to `1 ⊗ d x`. -/
abbrev sectionConormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalObj α U →ₗ[O₂.obj.obj U]
      ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.obj U :=
  Ideal.Cotangent.lift (conormalIdealToDifferentials φ α U)
    (conormalIdealToDifferentials_mul φ α U)

/-- The sectionwise conormal map as a morphism of objectwise module categories. -/
private abbrev sectionConormalHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ) :
    conormalObj α U ⟶
      ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.obj U :=
  ConcreteCategory.ofHom (C := ModuleCat (O₂.obj.obj U))
    (sectionConormalMap φ α U)

/-- Naturality of the sectionwise conormal map under restriction. -/
private theorem sectionConormalHom_naturality
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) {U V : Cᵒᵖ} (i : U ⟶ V) :
    (conormalPresheaf α).map i ≫
        (ModuleCat.restrictScalars
          (((ringSheaf J O₂).obj.map i).hom)).map
          (sectionConormalHom φ α V) =
      sectionConormalHom φ α U ≫
        ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.map i := sorry

/-- The presheaf morphism underlying the conormal map. -/
private def conormalPresheafHom
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalPresheaf α ⟶
      ((restrictionAlong α).obj (conormalTensorTerm φ α)).val where
  app U := sectionConormalHom φ α U
  naturality i := sectionConormalHom_naturality φ α i

/-- The conormal map viewed over the middle ring sheaf. -/
@[no_expose] noncomputable def conormalMapOverSource
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalSourceOverSource α ⟶
      (restrictionAlong α).obj (conormalTensorTerm φ α) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (ringSheaf J O₂).obj)).homEquiv
      (conormalPresheaf α)
      ((restrictionAlong α).obj (conormalTensorTerm φ α))).symm
    (conormalPresheafHom φ α)

/-- The canonical conormal map
`Ker(α) / Ker(α) ^ 2 ⟶ O₃ ⊗[O₂] Ω(O₂/O₁)`. -/
@[stacks 08TF "left map", stacks 08TS "left map"]
noncomputable def conormalMap
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalSource α ⟶ conormalTensorTerm φ α :=
  ((extendRestrictAdj α).homEquiv
      (conormalSourceOverSource α)
      (conormalTensorTerm φ α)).symm
    (conormalMapOverSource φ α)

/-- Under extension-restriction adjunction, the conormal map is the map induced by
`x ↦ 1 ⊗ d x` on the conormal presheaf. -/
@[simp]
theorem conormalMap_adj
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (extendRestrictAdj α).homEquiv
        (conormalSourceOverSource α) (conormalTensorTerm φ α)
        (conormalMap φ α) =
      conormalMapOverSource φ α := sorry

/-- The canonical commutative square comparing `φ` with `φ ≫ α`. -/
theorem conormalSquare
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    CommSq (𝟙 O₁) φ (φ ≫ α) α := sorry

/-- The canonical map
`O₃ ⊗[O₂] Ω(O₂/O₁) ⟶ Ω(O₃/O₁)` in the conormal sequence. -/
@[stacks 08TF "right map", stacks 08TS "right map"]
noncomputable def conormalToDifferentials
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalTensorTerm φ α ⟶ Ω(φ ≫ α) :=
  ((extendRestrictAdj α).homEquiv
      Ω(φ)
      Ω(φ ≫ α)).symm
    (RelativeDifferentials.map (conormalSquare φ α))

/-- Under extension-restriction adjunction, the right conormal morphism is the canonical map
on relative differentials induced by the square `conormalSquare φ α`. -/
@[simp]
theorem conormalToDifferentials_adj
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    (extendRestrictAdj α).homEquiv
        Ω(φ) Ω(φ ≫ α)
        (conormalToDifferentials φ α) =
      RelativeDifferentials.map (conormalSquare φ α) := sorry

/-- The two canonical maps in the conormal sequence have zero composite. -/
@[stacks 08TF "complex", stacks 08TS "complex"]
theorem conormal_comp_zero
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    conormalMap φ α ≫ conormalToDifferentials φ α = 0 := sorry

/-- The canonical conormal short complex associated to `O₁ ⟶ O₂ ⟶ O₃`. -/
@[stacks 08TF "conormal short complex", stacks 08TS "conormal short complex"]
noncomputable def conormalSequence
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) :
    ShortComplex (ringedSiteModuleCategory J O₃) :=
  ShortComplex.mk
      (conormalMap φ α)
      (conormalToDifferentials φ α)
      (conormal_comp_zero φ α)

/-- The conormal short complex of a locally surjective ring-sheaf morphism is exact. -/
@[stacks 08TF "exact conormal sequence", stacks 08TS "exact conormal sequence"]
theorem conormalSequence_exact
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective α] :
    (conormalSequence φ α).Exact := sorry

/-- The final map in the conormal sequence of a locally surjective morphism is epic. -/
@[stacks 08TF "conormal sequence epimorphism", stacks 08TS "conormal sequence epimorphism"]
instance conormalToDifferentials_epi
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) [Sheaf.IsLocallySurjective α] :
    Epi (conormalToDifferentials φ α) := sorry

/-- Explicit-hypothesis form of exactness of the conormal sequence. -/
theorem conormalSequence_exact_of_isLocallySurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (hα : Sheaf.IsLocallySurjective α) :
    (conormalSequence φ α).Exact := sorry

/-- Explicit-hypothesis form of epimorphicity of the final conormal-sequence morphism. -/
theorem conormalToDifferentials_epi_of_isLocallySurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (hα : Sheaf.IsLocallySurjective α) :
    Epi (conormalToDifferentials φ α) := sorry

/-- Sectionwise surjectivity is sufficient for exactness of the conormal sequence. -/
theorem conormalSequence_exact_of_sectionwiseSurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃)
    (hα : ∀ U : Cᵒᵖ, Function.Surjective ((α.hom.app U).hom)) :
    (conormalSequence φ α).Exact := sorry

/-- Sectionwise surjectivity makes the final conormal-sequence morphism epic. -/
theorem conormalToDifferentials_epi_of_sectionwiseSurjective
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃)
    (hα : ∀ U : Cᵒᵖ, Function.Surjective ((α.hom.app U).hom)) :
    Epi (conormalToDifferentials φ α) := sorry

/-- The canonical tensor `1 ⊗ d x` associated to a cotangent generator. -/
@[stacks 08TF "generator tensor", stacks 08TS "generator tensor"]
abbrev conormalGenerator
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (x : conormalIdeal α U) :
    ((restrictionAlong α).obj (conormalTensorTerm φ α)).val.obj U :=
  conormalGeneratorApply φ α U x

/-- On a cotangent generator, the sectionwise conormal map is `x ↦ 1 ⊗ d x`. -/
@[stacks 08TF "generator formula", stacks 08TS "generator formula"]
theorem sectionConormalMap_toCotangent
    (φ : O₁ ⟶ O₂) (α : O₂ ⟶ O₃) (U : Cᵒᵖ)
    (x : conormalIdeal α U) :
    sectionConormalMap φ α U ((conormalIdeal α U).toCotangent x) =
      conormalGenerator φ α U x := sorry

end SheafOfModules.RingedSite
