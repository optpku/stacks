/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import stacks_project.Chap96.Lemma_96_17_6_LowerShriek

/-!
# Module pushforward and higher direct images on associated τ-sites

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces, on
each associated `τ`-site, a module pushforward `f_*` as the chosen right adjoint
of `associatedModuleInverseImage`. Higher direct images are the right derived
functors of that pushforward, landing in `Mod(𝒴_τ, 𝒪_𝒴)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Module inverse image `f^*` along a 1-morphism of categories fibred in groupoids
is a left adjoint, so it admits a pushforward `f_*`. -/
instance associatedModuleInverseImage_isLeftAdjoint
    {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology) :
    (associatedModuleInverseImage f τ).IsLeftAdjoint :=
  sorry

/-- The underived module pushforward `f_* : Mod(𝒳_τ, 𝒪_𝒳) ⥤ Mod(𝒴_τ, 𝒪_𝒴)` along a
1-morphism `f : 𝒳 ⟶ 𝒴`, the chosen right adjoint of `associatedModuleInverseImage`. -/
abbrev associatedModulePushforward {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModuleInverseImage f τ).rightAdjoint

/-- `associatedModulePushforward f τ` is the chosen right adjoint of
`associatedModuleInverseImage f τ`. -/
theorem associatedModulePushforward_eq {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    associatedModulePushforward f τ = (associatedModuleInverseImage f τ).rightAdjoint :=
  rfl

/-- Module pushforward on associated `τ`-sites is additive. -/
instance associatedModulePushforward_additive {X Y : GroupoidsOver S} (f : X ⟶ Y)
    (τ : StandardTopology) :
    (associatedModulePushforward f τ).Additive :=
  sorry

variable {X Y : GroupoidsOver S} (f : X ⟶ Y) (τ : StandardTopology)
variable [HasInjectiveResolutions
    (SheafOfModules.{u + 1} (associatedStructureSheaf X τ))]

/-- The degree-`i` higher direct image functor `R^i f_*` on sheaves of modules. -/
abbrev associatedModuleHigherDirectImageFunctor (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf X τ) ⥤
      SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModulePushforward f τ).rightDerived i

/-- The degree-`i` higher direct image `R^i f_* F` of a sheaf of modules. -/
abbrev associatedModuleHigherDirectImage
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    SheafOfModules.{u + 1} (associatedStructureSheaf Y τ) :=
  (associatedModuleHigherDirectImageFunctor f τ i).obj F

/-- `associatedModuleHigherDirectImage f τ F i` is the object map of `rightDerived`
of module pushforward. -/
theorem associatedModuleHigherDirectImage_eq
    (F : SheafOfModules.{u + 1} (associatedStructureSheaf X τ)) (i : ℕ) :
    associatedModuleHigherDirectImage f τ F i =
      ((associatedModulePushforward f τ).rightDerived i).obj F :=
  rfl

end AlgebraicGeometry.GroupoidsOver
