/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.TensorProduct.NatInt
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk.Tensor
public import ReasLib.RingTheory.Localization.TensorProduct
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open scoped TensorProduct

noncomputable section

universe uA uσ

namespace AlgebraicGeometry.Proj.AssociatedModule.Tensor

open GradedModule.TensorProduct

variable {A : Type uA} {σ : Type uσ} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {M N : Type uA} [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N]
variable (ℳ : ℤ → Submodule ℤ M) (ℵ : ℤ → Submodule ℤ N)
variable [SetLike.GradedSMul 𝒜 ℳ] [SetLike.GradedSMul 𝒜 ℵ]

/-- The ordinary localized tensor comparison sends two degree-zero fractions to a degree-zero
fraction for the total tensor grading. -/
theorem localized_mem (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (y : AssociatedModule.localization 𝒜 ℵ P) :
    LocalizedModule.tensorProductLinearEquiv P
        ((x : LocalizedModule P M) ⊗ₜ[Localization P] (y : LocalizedModule P N)) ∈
      AssociatedModule.localization 𝒜 (grading A ℳ ℵ) P := sorry

/-- The value of the localized tensor pairing on two degree-zero homogeneous fractions. -/
noncomputable def localizedValue (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (y : AssociatedModule.localization 𝒜 ℵ P) :
    AssociatedModule.localization 𝒜 (grading A ℳ ℵ) P :=
  ⟨LocalizedModule.tensorProductLinearEquiv P
      ((x : LocalizedModule P M) ⊗ₜ[Localization P] (y : LocalizedModule P N)),
    localized_mem 𝒜 ℳ ℵ P x y⟩

/-- The localized tensor value is additive in its second argument. -/
theorem localizedValue_add_right (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (y z : AssociatedModule.localization 𝒜 ℵ P) :
    localizedValue 𝒜 ℳ ℵ P x (y + z) =
      localizedValue 𝒜 ℳ ℵ P x y + localizedValue 𝒜 ℳ ℵ P x z := sorry

/-- The localized tensor value is linear in its second argument. -/
theorem localizedValue_smul_right (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (r : HomogeneousLocalization 𝒜 P)
    (y : AssociatedModule.localization 𝒜 ℵ P) :
    localizedValue 𝒜 ℳ ℵ P x (r • y) =
      r • localizedValue 𝒜 ℳ ℵ P x y := sorry
/-- Fixing the first fraction gives the canonical localized linear map in the second input. -/
noncomputable def localizedRight (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P) :
    AssociatedModule.localization 𝒜 ℵ P →ₗ[HomogeneousLocalization 𝒜 P]
      AssociatedModule.localization 𝒜 (grading A ℳ ℵ) P where
  toFun := localizedValue 𝒜 ℳ ℵ P x
  map_add' := localizedValue_add_right 𝒜 ℳ ℵ P x
  map_smul' := localizedValue_smul_right 𝒜 ℳ ℵ P x


/-- The localized tensor value is additive in its first argument. -/
theorem localizedValue_add_left (P : Submonoid A)
    (x y : AssociatedModule.localization 𝒜 ℳ P)
    (z : AssociatedModule.localization 𝒜 ℵ P) :
    localizedValue 𝒜 ℳ ℵ P (x + y) z =
      localizedValue 𝒜 ℳ ℵ P x z + localizedValue 𝒜 ℳ ℵ P y z := sorry

/-- The localized tensor value is linear in its first argument. -/
theorem localizedValue_smul_left (P : Submonoid A)
    (r : HomogeneousLocalization 𝒜 P)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (y : AssociatedModule.localization 𝒜 ℵ P) :
    localizedValue 𝒜 ℳ ℵ P (r • x) y =
      r • localizedValue 𝒜 ℳ ℵ P x y := sorry

/-- The localized right-input linear map is additive in its fixed first input. -/
theorem localizedRight_add (P : Submonoid A)
    (x y : AssociatedModule.localization 𝒜 ℳ P) :
    localizedRight 𝒜 ℳ ℵ P (x + y) =
      localizedRight 𝒜 ℳ ℵ P x + localizedRight 𝒜 ℳ ℵ P y := sorry

/-- The localized right-input linear map is linear in its fixed first input. -/
theorem localizedRight_smul (P : Submonoid A)
    (r : HomogeneousLocalization 𝒜 P)
    (x : AssociatedModule.localization 𝒜 ℳ P) :
    localizedRight 𝒜 ℳ ℵ P (r • x) =
      r • localizedRight 𝒜 ℳ ℵ P x := sorry


/-- The degree-zero localized bilinear pairing induced by the ordinary localization-tensor
comparison. -/
noncomputable def localizedPairing (P : Submonoid A) :
    AssociatedModule.localization 𝒜 ℳ P →ₗ[HomogeneousLocalization 𝒜 P]
      AssociatedModule.localization 𝒜 ℵ P →ₗ[HomogeneousLocalization 𝒜 P]
        AssociatedModule.localization 𝒜 (grading A ℳ ℵ) P where
  toFun := localizedRight 𝒜 ℳ ℵ P
  map_add' := localizedRight_add 𝒜 ℳ ℵ P
  map_smul' := localizedRight_smul 𝒜 ℳ ℵ P
/-- The canonical map from the tensor product of two degree-zero homogeneous localizations to
the degree-zero localization of the graded tensor product. -/
@[stacks 01MK "localized tensor comparison"]
noncomputable def localizedMap (P : Submonoid A) :
    AssociatedModule.localization 𝒜 ℳ P ⊗[HomogeneousLocalization 𝒜 P]
        AssociatedModule.localization 𝒜 ℵ P →ₗ[HomogeneousLocalization 𝒜 P]
      AssociatedModule.localization 𝒜 (grading A ℳ ℵ) P :=
  TensorProduct.lift (localizedPairing 𝒜 ℳ ℵ P)

/-- On a pure localized tensor, `localizedMap` is the ordinary localization-tensor
comparison. -/
theorem localizedMap_tmul (P : Submonoid A)
    (x : AssociatedModule.localization 𝒜 ℳ P)
    (y : AssociatedModule.localization 𝒜 ℵ P) :
    localizedMap 𝒜 ℳ ℵ P
        (x ⊗ₜ[HomogeneousLocalization 𝒜 P] y) =
      ⟨LocalizedModule.tensorProductLinearEquiv P
          ((x : LocalizedModule P M) ⊗ₜ[Localization P] (y : LocalizedModule P N)),
        localized_mem 𝒜 ℳ ℵ P x y⟩ := sorry

/-- The localized tensor comparison on a positive standard open. -/
noncomputable def awayMap {d : ℕ} (f : 𝒜 d) :
    AssociatedModule.away 𝒜 ℳ f ⊗[HomogeneousLocalization.Away 𝒜 (f : A)] AssociatedModule.away 𝒜 ℵ f
      →ₗ[HomogeneousLocalization.Away 𝒜 (f : A)] AssociatedModule.away 𝒜 (grading A ℳ ℵ) f :=
  localizedMap 𝒜 ℳ ℵ (Submonoid.powers (f : A))

/-- On pure tensors, the standard-open comparison is the localized tensor comparison. -/
theorem awayMap_tmul {d : ℕ} (f : 𝒜 d) (x : AssociatedModule.away 𝒜 ℳ f)
    (y : AssociatedModule.away 𝒜 ℵ f) :
    awayMap 𝒜 ℳ ℵ f
        (x ⊗ₜ[HomogeneousLocalization.Away 𝒜 (f : A)] y) =
      localizedMap 𝒜 ℳ ℵ (Submonoid.powers (f : A))
        (x ⊗ₜ[HomogeneousLocalization.Away 𝒜 (f : A)] y) := sorry

/-- The localized tensor comparison at the homogeneous prime represented by `x`. -/
noncomputable def atPointMap (x : AlgebraicGeometry.Proj 𝒜) :
    AssociatedModule.atPoint 𝒜 ℳ x ⊗[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        AssociatedModule.atPoint 𝒜 ℵ x →ₗ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
      AssociatedModule.atPoint 𝒜 (grading A ℳ ℵ) x :=
  localizedMap 𝒜 ℳ ℵ x.asHomogeneousIdeal.toIdeal.primeCompl

/-- On pure tensors, the point comparison is the localized tensor comparison at the point's
homogeneous-prime complement. -/
theorem atPointMap_tmul (x : AlgebraicGeometry.Proj 𝒜)
    (m : AssociatedModule.atPoint 𝒜 ℳ x) (n : AssociatedModule.atPoint 𝒜 ℵ x) :
    atPointMap 𝒜 ℳ ℵ x
        (m ⊗ₜ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl] n) =
      localizedMap 𝒜 ℳ ℵ x.asHomogeneousIdeal.toIdeal.primeCompl
        (m ⊗ₜ[HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl] n) := sorry

/-- Pointwise localized tensoring of two associated sections is locally representable. -/
theorem sectionValue_isLocallyRepresentable
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U) (t : AssociatedModule.sections 𝒜 ℵ U) :
    AssociatedModule.IsLocallyRepresentable 𝒜 (grading A ℳ ℵ) U
      (fun x ↦ atPointMap 𝒜 ℳ ℵ x.1
        (s.1 x ⊗ₜ[HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl] t.1 x)) := sorry

/-- The associated section obtained by pointwise localized tensoring. -/
noncomputable def sectionValue
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U) (t : AssociatedModule.sections 𝒜 ℵ U) :
    AssociatedModule.sections 𝒜 (grading A ℳ ℵ) U :=
  ⟨fun x ↦ atPointMap 𝒜 ℳ ℵ x.1
      (s.1 x ⊗ₜ[HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl] t.1 x),
    sectionValue_isLocallyRepresentable 𝒜 ℳ ℵ U s t⟩

/-- Associated tensor sections evaluate pointwise by the localized tensor comparison. -/
theorem sectionValue_apply
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U) (t : AssociatedModule.sections 𝒜 ℵ U) (x : U) :
    (sectionValue 𝒜 ℳ ℵ U s t).1 x =
      atPointMap 𝒜 ℳ ℵ x.1
        (s.1 x ⊗ₜ[HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl] t.1 x) := sorry

variable [decompM : DirectSum.Decomposition ℳ] [decompN : DirectSum.Decomposition ℵ]

include decompM decompN

/-- The associated tensor-section pairing is additive in its second argument. -/
theorem sectionValue_add_right
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U)
    (t₁ t₂ : AssociatedModule.sections 𝒜 ℵ U) :
    sectionValue 𝒜 ℳ ℵ U s (t₁ + t₂) =
      sectionValue 𝒜 ℳ ℵ U s t₁ + sectionValue 𝒜 ℳ ℵ U s t₂ := sorry

/-- The associated tensor-section pairing is linear in its second argument. -/
theorem sectionValue_smul_right
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (t : AssociatedModule.sections 𝒜 ℵ U) :
    sectionValue 𝒜 ℳ ℵ U s (r • t) =
      r • sectionValue 𝒜 ℳ ℵ U s t := sorry

/-- Fixing the first section gives the canonical linear map in the second section input. -/
noncomputable def right
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : AssociatedModule.sections 𝒜 ℳ U) :
    AssociatedModule.sections 𝒜 ℵ U →ₗ[(AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U)]
      AssociatedModule.sections 𝒜 (grading A ℳ ℵ) U where
  toFun := sectionValue 𝒜 ℳ ℵ U s
  map_add' := sectionValue_add_right 𝒜 ℳ ℵ U s
  map_smul' := sectionValue_smul_right 𝒜 ℳ ℵ U s


/-- The associated tensor-section pairing is additive in its first argument. -/
theorem sectionValue_add_left
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s₁ s₂ : AssociatedModule.sections 𝒜 ℳ U)
    (t : AssociatedModule.sections 𝒜 ℵ U) :
    sectionValue 𝒜 ℳ ℵ U (s₁ + s₂) t =
      sectionValue 𝒜 ℳ ℵ U s₁ t + sectionValue 𝒜 ℳ ℵ U s₂ t := sorry

/-- The associated tensor-section pairing is linear in its first argument. -/
theorem sectionValue_smul_left
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (s : AssociatedModule.sections 𝒜 ℳ U)
    (t : AssociatedModule.sections 𝒜 ℵ U) :
    sectionValue 𝒜 ℳ ℵ U (r • s) t =
      r • sectionValue 𝒜 ℳ ℵ U s t := sorry

/-- The right-input section map is additive in its fixed first section. -/
theorem right_add
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s₁ s₂ : AssociatedModule.sections 𝒜 ℳ U) :
    right 𝒜 ℳ ℵ U (s₁ + s₂) =
      right 𝒜 ℳ ℵ U s₁ + right 𝒜 ℳ ℵ U s₂ := sorry

/-- The right-input section map is linear in its fixed first section. -/
theorem right_smul
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (r : (AlgebraicGeometry.Proj 𝒜).presheaf.obj (op U))
    (s : AssociatedModule.sections 𝒜 ℳ U) :
    right 𝒜 ℳ ℵ U (r • s) =
      r • right 𝒜 ℳ ℵ U s := sorry


/-- The associated tensor-section pairing commutes with restriction of sections. -/
theorem sectionValue_naturality
    {U V : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (i : U ⟶ V)
    (s : (AssociatedModule.sheaf 𝒜 ℳ).val.obj U)
    (t : (AssociatedModule.sheaf 𝒜 ℵ).val.obj U) :
    (AssociatedModule.sheaf 𝒜 (grading A ℳ ℵ)).val.map i
        (sectionValue 𝒜 ℳ ℵ U.unop s t) =
      sectionValue 𝒜 ℳ ℵ V.unop
        ((AssociatedModule.sheaf 𝒜 ℳ).val.map i s)
        ((AssociatedModule.sheaf 𝒜 ℵ).val.map i t) := sorry

/-- The restriction-compatible sectionwise bilinear pairing defining the associated-sheaf
tensor morphism. -/
noncomputable def bilinear :
    PresheafOfModules.BilinearMap (AlgebraicGeometry.Proj 𝒜).sheaf.obj
      (AssociatedModule.sheaf 𝒜 ℳ).val (AssociatedModule.sheaf 𝒜 ℵ).val
        (AssociatedModule.sheaf 𝒜 (grading A ℳ ℵ)).val where
  app U :=
    { toFun := right 𝒜 ℳ ℵ U.unop
      map_add' := right_add 𝒜 ℳ ℵ U.unop
      map_smul' := right_smul 𝒜 ℳ ℵ U.unop }
  naturality := sectionValue_naturality 𝒜 ℳ ℵ

/-- The canonical morphism from the tensor product of two associated graded-module sheaves to
the sheaf associated to their graded tensor product. -/
@[stacks 01MK "associated-sheaf tensor comparison"]
noncomputable def hom :
    (tensorObj (AssociatedModule.sheaf 𝒜 ℳ) (AssociatedModule.sheaf 𝒜 ℵ) :
      (AlgebraicGeometry.Proj 𝒜).Modules) ⟶
        AssociatedModule.sheaf 𝒜 (grading A ℳ ℵ) :=
  SheafOfModules.RingedSite.SectionBilinearMap.hom
    (O := (AlgebraicGeometry.Proj 𝒜).sheaf) (bilinear 𝒜 ℳ ℵ)

/-- The associated tensor morphism sends a pure tensor section to the pointwise localized
tensor section. -/
theorem hom_tensorSection
    (U : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ)
    (s : (AssociatedModule.sheaf 𝒜 ℳ).val.obj U)
    (t : (AssociatedModule.sheaf 𝒜 ℵ).val.obj U) :
    ((hom 𝒜 ℳ ℵ).val.app U).hom
        (tensorSection (AlgebraicGeometry.Proj 𝒜).sheaf U s t) =
      sectionValue 𝒜 ℳ ℵ U.unop s t := sorry

end AlgebraicGeometry.Proj.AssociatedModule.Tensor
