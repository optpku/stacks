/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import stacks_project.Chap96.«96_7_1_1_InverseImage»
public import stacks_project.Chap96.Lemma_96_11_4_Comparison
public import stacks_project.Chap96.Lemma_96_12_3_Pullback
public import stacks_project.Chap96.Lemma_96_12_5_AssociatedModules
public import stacks_project.Chap100.Definition_100_4_2_Points
public import stacks_project.Chap103.Definition_103_9_1_Parasitic
public import stacks_project.Chap103.«103_15_1_1_Smooth»
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Stability of parasitic modules on algebraic stacks

Parasitic vanishing of `𝒪_X`-modules is stable under inverse image along a
flat morphism of algebraic stacks, under `τ`-sheafification, and under descent
along jointly point-covering smooth (resp. flat and locally finitely presented)
families.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

noncomputable section

universe u v

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Lemma 103.9.2 (1): if `F` is a parasitic presheaf of `𝒪_X`-modules and
`g : Y ⟶ X` is a flat morphism of algebraic stacks, then the inverse image
`g⁻¹ F` is parasitic. -/
@[stacks 0774]
instance instIsParasitic_presheafModuleInverseImage
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (g : Y ⟶ X) [AlgebraicStack.Flat g]
    (F : PresheafOfModules.{u} (structureSheaf X).obj) [IsParasitic F] :
    IsParasitic ((presheafModuleInverseImage g).obj F) :=
  sorry

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
        (associatedStructurePresheafIso X τ).hom).obj F.val :=
  sorry

/-- Lemma 103.9.2 (2): for `τ` among Zariski, étale, smooth, syntomic, and fppf,
the `τ`-sheafification of a parasitic presheaf of `𝒪_X`-modules is parasitic. -/
@[stacks 0774]
theorem isParasitic_sheafification {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : PresheafOfModules.{u} (structureSheaf X).obj)
    [IsParasitic F] :
    IsParasitic (associatedModulePresheaf
      ((PresheafOfModules.sheafification.{u}
        (associatedStructurePresheafIso X τ).hom).obj F)) :=
  sorry

/-- The category of sheaves of modules on `(X_τ, 𝒪_X)` is abelian. -/
instance associatedModulesAbelian (X : GroupoidsOver S) (τ : StandardTopology) :
    Abelian (associatedModules X τ) where
  toPreadditive := inferInstance
  toIsNormalMonoCategory := sorry
  toIsNormalEpiCategory := sorry
  has_finite_products := sorry
  has_kernels := sorry
  has_cokernels := sorry

/-- The object property of parasitic objects of `Mod(X_τ, 𝒪_X)`. -/
abbrev associatedModules.parasitic (X : GroupoidsOver S) [AlgebraicStack X]
    (τ : StandardTopology) : ObjectProperty (associatedModules X τ) :=
  fun F ↦ IsParasitic (associatedModulePresheaf F)

/-- Membership in `associatedModules.parasitic` is parasitic vanishing of the
underlying module presheaf. -/
theorem associatedModules.mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (τ : StandardTopology) (F : associatedModules X τ) :
    associatedModules.parasitic X τ F ↔
      IsParasitic (associatedModulePresheaf F) :=
  sorry

/-- Lemma 103.9.2 (3): for `τ` among Zariski, étale, smooth, syntomic, and fppf,
parasitic objects of `Mod(X_τ, 𝒪_X)` form a Serre subcategory. -/
@[stacks 0774]
instance associatedModules.instParasitic_isSerreClass
    (X : GroupoidsOver S) [AlgebraicStack X] (τ : StandardTopology) :
    IsSerreClass (associatedModules.parasitic X τ) :=
  sorry

/-- Lemma 103.9.2 (4): if `F` is an étale `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of smooth morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
@[stacks 0774]
theorem isParasitic_of_forall_smooth_pullback {X : GroupoidsOver S}
    [AlgebraicStack X] {ι : Type v} {Xi : ι → GroupoidsOver S}
    [∀ i, AlgebraicStack (Xi i)] (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Smooth (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : etaleModules X)
    (hF : ∀ i,
      IsParasitic (etaleModulePresheaf ((moduleInverseImage (f i)).obj F))) :
    IsParasitic (etaleModulePresheaf F) :=
  sorry

/-- Lemma 103.9.2 (5): if `F` is an fppf `𝒪_X`-module and `f i : Xi i ⟶ X` is a
family of flat and locally finitely presented morphisms of algebraic stacks with
`|X| = ⋃ |f i|(|Xi i|)`, and each inverse image `(f i)⁻¹ F` is parasitic, then
`F` is parasitic. -/
@[stacks 0774]
theorem isParasitic_of_forall_flat_locallyOfFinitePresentation_pullback
    {X : GroupoidsOver S} [AlgebraicStack X] {ι : Type v}
    {Xi : ι → GroupoidsOver S} [∀ i, AlgebraicStack (Xi i)]
    (f : ∀ i, Xi i ⟶ X) [∀ i, AlgebraicStack.Flat (f i)]
    [∀ i, AlgebraicStack.LocallyOfFinitePresentation (f i)]
    (h_cover : ∀ y : AlgebraicStack.Points X,
      ∃ i, y ∈ Set.range (AlgebraicStack.Points.map (f i)))
    (F : SheafOfModules.{u} (structureSheaf X))
    (hF : ∀ i, IsParasitic ((presheafModuleInverseImage (f i)).obj F.val)) :
    IsParasitic F.val :=
  sorry

end AlgebraicGeometry.GroupoidsOver
