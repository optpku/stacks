/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.ParasiticCohomology
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
import StacksCheckRecall

/-!
# Vanishing and pushforward of parasitic modules on algebraic stacks

Parasitic modules have vanishing cohomology and parasitic higher direct images
in the étale and fppf topologies.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Algebraic-stack atlases give small sections in the étale and fppf topologies,
using the same underlying presheaf after restriction to the étale topology. -/
theorem hasSmallAssociatedTypeSections_of_etale_or_fppf
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf) :
    HasSmallAssociatedTypeSections f τ := by
  rcases hτ with rfl | rfl
  · exact ⟨fun F Z ↦ AlgebraicStack.EtaleSmallSections.sectionsSmall f F Z.unop⟩
  · exact ⟨fun F Z ↦ AlgebraicStack.EtaleSmallSections.sectionsSmall f
      ⟨F.obj, Presheaf.IsSheaf.of_le (etaleTopology_le_fppfTopology X) F.property⟩ Z.unop⟩

/-- Morphisms of algebraic stacks have small associated type-valued sections
in the étale topology. -/
instance hasSmallAssociatedTypeSections_etale_of_algebraicStack
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : HasSmallAssociatedTypeSections f .etale :=
  hasSmallAssociatedTypeSections_of_etale_or_fppf f (Or.inl rfl)

/-- Morphisms of algebraic stacks have small associated type-valued sections
in the fppf topology. -/
instance hasSmallAssociatedTypeSections_fppf_of_algebraicStack
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) : HasSmallAssociatedTypeSections f .fppf :=
  hasSmallAssociatedTypeSections_of_etale_or_fppf f (Or.inr rfl)

section Cohomology

variable {X : GroupoidsOver S} [AlgebraicStack X]
variable {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf)
variable [Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
variable (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ))
variable [IsParasitic ((PresheafOfModules.restrictScalars
  (associatedStructurePresheafIso X τ).hom).obj F.val)]
variable (i : ℕ) [HasExt (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]

/- Lemma 103.9.3 (1): a parasitic module on an algebraic stack has vanishing
cohomology in every degree for the étale or fppf topology. -/
@[stacks 0775] #check
  (AlgebraicGeometry.GroupoidsOver.isZero_cohomology_of_isParasitic hτ F i :
    IsZero (RingedSite.Hom.moduleGlobalCohomology (X := associatedRingedSite X τ) F i))

end Cohomology

section HigherDirectImage

variable {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
variable {τ : StandardTopology} (hτ : τ = .etale ∨ τ = .fppf) (f : X ⟶ Y)
variable [Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]
variable [Abelian (RingedSite.ModuleCat.{u} (associatedRingedSite Y τ))]
variable (F : RingedSite.ModuleCat.{u} (associatedRingedSite X τ))
variable [IsParasitic ((PresheafOfModules.restrictScalars
  (associatedStructurePresheafIso X τ).hom).obj F.val)]
variable (i : ℕ)
variable [HasInjectiveResolutions (RingedSite.ModuleCat.{u} (associatedRingedSite X τ))]

/- Lemma 103.9.3 (2): every higher direct image of a parasitic module along a
morphism of algebraic stacks is parasitic in the étale or fppf topology. -/
@[stacks 0775] #check
  (AlgebraicGeometry.GroupoidsOver.associatedModules.isParasitic_higherDirectImage
    (hsize := hasSmallAssociatedTypeSections_of_etale_or_fppf f hτ) hτ f F i :
    IsParasitic ((PresheafOfModules.restrictScalars
      (associatedStructurePresheafIso Y τ).hom).obj
        (associatedModules.higherDirectImage f τ
          (hsize := hasSmallAssociatedTypeSections_of_etale_or_fppf f hτ) F i).val))

end HigherDirectImage

end AlgebraicGeometry.GroupoidsOver
