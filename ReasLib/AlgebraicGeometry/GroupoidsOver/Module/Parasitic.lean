/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Parasitic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.PresheafModule
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.LocallyQuasiCoherent
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic

/-! # Stability and descent of parasitic modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- If `F` is a parasitic presheaf of `𝒪_X`-modules and
`g : Y ⟶ X` is a flat morphism of algebraic stacks, then the inverse image
`g⁻¹ F` is parasitic. -/
instance IsParasitic.inverseImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) [AlgebraicStack.Flat g]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) [IsParasitic F] :
    IsParasitic ((presheafModuleInverseImage g).obj F) := sorry

/-- The underlying module presheaf of an object of `Mod(X_τ, 𝒪_X)`, as a
presheaf of modules over the fppf structure sheaf of `X`. -/
def associatedModulePresheaf {X : GroupoidsOver S} {τ : StandardTopology}
    (F : associatedModules X τ) :
    PresheafOfModules.{u} (structureSheaf X).obj :=
  (PresheafOfModules.restrictScalars (associatedStructurePresheafIso X τ).hom).obj F.val

/-- `associatedModulePresheaf F` is restriction of scalars of `F.val` along
`associatedStructurePresheafIso.hom`. -/
theorem associatedModulePresheaf_eq {X : GroupoidsOver S} {τ : StandardTopology}
    (F : associatedModules X τ) :
    associatedModulePresheaf F =
      (PresheafOfModules.restrictScalars
        (associatedStructurePresheafIso X τ).hom).obj F.val := sorry

/-- For `τ` among Zariski, étale, smooth, syntomic, and fppf,
the `τ`-sheafification of a parasitic presheaf of `𝒪_X`-modules is parasitic. -/
instance IsParasitic.sheafification {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [IsParasitic F] :
    IsParasitic (associatedModulePresheaf
      ((PresheafOfModules.sheafification.{u}
        (associatedStructurePresheafIso X τ).hom).obj F)) := sorry

/-- The object property of parasitic objects of `Mod(X_τ, 𝒪_X)`. -/
abbrev associatedModules.parasitic (X : GroupoidsOver S) [AlgebraicStack X]
    (τ : StandardTopology) : ObjectProperty (associatedModules X τ) :=
  fun F ↦ IsParasitic (associatedModulePresheaf F)

/-- Membership in `associatedModules.parasitic` is parasitic vanishing of the
underlying module presheaf. -/
theorem associatedModules.mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : associatedModules X τ) :
    associatedModules.parasitic X τ F ↔
      IsParasitic (associatedModulePresheaf F) := sorry

/-- For `τ` among Zariski, étale, smooth, syntomic, and fppf,
parasitic objects of `Mod(X_τ, 𝒪_X)` form a Serre subcategory. -/
instance associatedModules.parasiticIsSerreClass
    (X : GroupoidsOver S) [AlgebraicStack X] (τ : StandardTopology) :
    IsSerreClass (associatedModules.parasitic X τ) := sorry

/-- If `F` is an étale `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of smooth morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
theorem IsParasitic.ofSmoothCover {X : GroupoidsOver S}
    [AlgebraicStack X] {ι : Type v} {Xi : ι → GroupoidsOver S}
    [∀ i, AlgebraicStack (Xi i)] (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : etaleModules X)
    (hF : ∀ i,
      IsParasitic (etaleModulePresheaf ((etaleModuleInverseImage (f i)).obj F))) :
    IsParasitic (etaleModulePresheaf F) := sorry

/-- If `F` is an fppf `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
theorem IsParasitic.ofFppfCover
    {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
    {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Flat (f i)]
    [∀ i, AlgebraicStack.LocallyOfFinitePresentation (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (hF : ∀ i, IsParasitic ((presheafModuleInverseImage (f i)).obj F.val)) :
    IsParasitic F.val := sorry

end AlgebraicGeometry.GroupoidsOver
