module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor products of module sections

This leaf owns the pure tensor of two global sections of module sheaves on a
ringed space. It is independent of invertibility, tensor powers, and any
chosen projective-spectrum presentation.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pointwise pure tensors of compatible global-section families are compatible with restriction
maps. -/
theorem tensorSection_isCompatible
    {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections)
    ⦃U V : (Opens X)ᵒᵖ⦄ (i : U ⟶ V) :
    (tensorObj ℱ 𝒢).val.map i
        (SheafOfModules.RingedSite.tensorSection X.sheaf U (s.1 U) (t.1 U)) =
      SheafOfModules.RingedSite.tensorSection X.sheaf V (s.1 V) (t.1 V) := sorry

/-- The pure tensor of two global sections, viewed as a global section of the tensor-product
module. -/
@[stacks 03L6 "compatible pure tensor of global module-sheaf sections"]
noncomputable def tensorSection
    {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) :
    (ℱ ⊗ 𝒢).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ SheafOfModules.RingedSite.tensorSection X.sheaf U (s.1 U) (t.1 U))
    (tensorSection_isCompatible (X := X) (ℱ := ℱ) (𝒢 := 𝒢) s t)

/-- Evaluation of a global pure tensor section is the generic pointwise pure tensor. -/
@[simp]
theorem tensorSection_apply
    {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) (U : (Opens X)ᵒᵖ) :
    (tensorSection s t).1 U =
      SheafOfModules.RingedSite.tensorSection X.sheaf U (s.1 U) (t.1 U) := sorry

/-- The structure-module morphism classified by a pure tensor section is the tensor product of
the morphisms classified by its two factors. -/
theorem topSectionMorphism_tensorSection
    {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) :
    topSectionMorphism (ℱ ⊗ 𝒢)
        (sectionsEquivTop (ℱ ⊗ 𝒢) (tensorSection s t)) =
      (unitIsoTensorUnit X).hom ≫ (λ_ (𝟙_ X.Modules)).inv ≫
        (((unitIsoTensorUnit X).inv ≫
            topSectionMorphism ℱ (sectionsEquivTop ℱ s)) ⊗ₘ
          ((unitIsoTensorUnit X).inv ≫
            topSectionMorphism 𝒢 (sectionsEquivTop 𝒢 t))) := sorry

/-- Pure tensor sections are natural in both module-sheaf arguments. -/
@[simp]
theorem sectionsMap_tensorSection
    {ℱ₁ ℱ₂ 𝒢₁ 𝒢₂ : X.Modules} (f : ℱ₁ ⟶ ℱ₂) (g : 𝒢₁ ⟶ 𝒢₂)
    (s : ℱ₁.sections) (t : 𝒢₁.sections) :
    SheafOfModules.sectionsMap (f ⊗ₘ g) (tensorSection s t) =
      tensorSection (SheafOfModules.sectionsMap f s) (SheafOfModules.sectionsMap g t) := sorry

/-- Reassociating a pure tensor section is induced by the monoidal associator. -/
theorem tensorSection_assoc
    {ℱ 𝒢 ℋ : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) (u : ℋ.sections) :
    SheafOfModules.sectionsMap (α_ ℱ 𝒢 ℋ).hom (tensorSection (tensorSection s t) u) =
      tensorSection s (tensorSection t u) := sorry

/-- Swapping a pure tensor section is induced by the symmetric braiding. -/
theorem tensorSection_braiding
    [SymmetricCategory X.Modules] {ℱ 𝒢 : X.Modules} (s : ℱ.sections) (t : 𝒢.sections) :
    SheafOfModules.sectionsMap (β_ ℱ 𝒢).hom (tensorSection s t) = tensorSection t s := sorry


/- The section values come from the generic pointwise tensor construction. Its residual `sorryAx`
is inherited from the Prop-valued monoidal-localization closure witness; this global construction
also carries the Prop-valued restriction-compatibility proof above. -/

end AlgebraicGeometry.RingedSpace
