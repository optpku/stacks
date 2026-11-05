/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Original-universe generators of algebraic-space modules

The full chart site has large objects, but its displayed dense atlas charts have an actual
small index. Sheafification of free represented modules on those charts gives a generator
without changing the module section universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.AtlasGenerator

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The genuinely small chart index attached to the atlas already in the input space. -/
abbrev Index : Type u := PullbackFactory.SmallAtlas.Index (AtlasInput.scheme X)

/-- The full-site object represented by an actual member of that chart family. -/
def chart (i : Index X) : smallEtaleSite X :=
  PullbackFactory.SmallAtlas.object (AtlasInput.scheme X) (AtlasInput.map X) i

/-- A free module presheaf represented by the specified chart, in section universe `u`. -/
def freeRepresentable (i : Index X) : PresheafOfModules.{u} (structureSheaf X).obj :=
  (PresheafOfModules.free (structureSheaf X).obj).obj (yoneda.obj (chart X i))

/-- The actual small coproduct of all displayed free represented chart modules. -/
def presheafGenerator : PresheafOfModules.{u} (structureSheaf X).obj :=
  ∐ freeRepresentable X

/-- Sheafification uses the existing actual original-universe adjunction. -/
def generator : X.Modules :=
  (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf X).obj)).obj (presheafGenerator X)

/-- The original free represented Hom correspondence evaluates at the chart identity. -/
def representedHomEquiv (i : Index X) (M : PresheafOfModules.{u} (structureSheaf X).obj) :
    (freeRepresentable X i ⟶ M) ≃ M.obj (op (chart X i)) :=
  PresheafOfModules.freeYonedaEquiv

/-- A morphism code consists of its actual section functions on the same small chart family. -/
abbrev MapCode (M N : X.Modules) : Type u :=
  ∀ i : Index X, M.val.obj (op (chart X i)) → N.val.obj (op (chart X i))

/-- Encode the supplied module map by restricting its original section functions. -/
def sectionFunctions {M N : X.Modules} (f : M ⟶ N) : MapCode X M N :=
  fun i x ↦ f.val.app (op (chart X i)) x

/-- Dense chart coverage and sheaf separation make the actual section code injective. -/
theorem sectionFunctions_injective (M N : X.Modules) :
    Function.Injective (sectionFunctions X (M := M) (N := N)) := by
  intro firstMap secondMap equality
  let atlasInclusion := PullbackFactory.SmallAtlas.inclusion (AtlasInput.scheme X) (AtlasInput.map X)
  letI := PullbackFactory.SmallAtlas.inclusion_coverDense
    (AtlasInput.scheme X) (AtlasInput.map X) (AtlasInput.locallySurjective X)
  ext chartObject sectionValue
  apply Functor.IsCoverDense.ext atlasInclusion
    ((sheafCompose (smallEtaleTopology X) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf (structureSheaf X)).obj N)) chartObject.unop
  intro index restrictionMap
  have firstNaturality := CategoryTheory.congr_fun (firstMap.val.naturality restrictionMap.op) sectionValue
  have secondNaturality := CategoryTheory.congr_fun (secondMap.val.naturality restrictionMap.op) sectionValue
  exact firstNaturality.symm.trans
    ((congrFun (congrFun equality index) (M.val.map restrictionMap.op sectionValue)).trans secondNaturality)

/-- The actual small-atlas free generator separates maps on the full chart site. -/
theorem generator_isSeparator : IsSeparator (generator X) := by
  classical
  rw [isSeparator_def]
  intro sourceModule targetModule firstMap secondMap equality
  apply sectionFunctions_injective X sourceModule targetModule
  funext index sectionValue
  let freeMap := (representedHomEquiv X index sourceModule.val).symm sectionValue
  let generatorMap := Sigma.desc (fun otherIndex ↦
    if indexEquality : otherIndex = index then
      eqToHom (congrArg (freeRepresentable X) indexEquality) ≫ freeMap else 0)
  let sheafificationAdj := PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (structureSheaf X).obj)
  have mappedEquality := congrArg (sheafificationAdj.homEquiv _ targetModule)
    (equality ((sheafificationAdj.homEquiv _ sourceModule).symm generatorMap))
  have firstNaturality := sheafificationAdj.homEquiv_naturality_right
    ((sheafificationAdj.homEquiv _ sourceModule).symm generatorMap) firstMap
  have secondNaturality := sheafificationAdj.homEquiv_naturality_right
    ((sheafificationAdj.homEquiv _ sourceModule).symm generatorMap) secondMap
  have presheafEquality := firstNaturality.symm.trans (mappedEquality.trans secondNaturality)
  rw [(sheafificationAdj.homEquiv _ sourceModule).apply_symm_apply generatorMap]
    at presheafEquality
  have componentEquality := congrArg (fun moduleMap ↦ Sigma.ι (freeRepresentable X) index ≫ moduleMap)
    presheafEquality
  dsimp only [generatorMap] at componentEquality
  erw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc] at componentEquality
  simp only [dif_pos rfl, eqToHom_refl, Category.id_comp] at componentEquality
  change freeMap ≫ firstMap.val = freeMap ≫ secondMap.val at componentEquality
  have valueEquality := congrArg (representedHomEquiv X index targetModule.val) componentEquality
  change PresheafOfModules.freeYonedaEquiv (freeMap ≫ firstMap.val) =
    PresheafOfModules.freeYonedaEquiv (freeMap ≫ secondMap.val) at valueEquality
  rw [PresheafOfModules.freeYonedaEquiv_comp, PresheafOfModules.freeYonedaEquiv_comp] at valueEquality
  have freeValue : PresheafOfModules.freeYonedaEquiv freeMap = sectionValue :=
    (representedHomEquiv X index sourceModule.val).apply_symm_apply sectionValue
  rw [freeValue] at valueEquality
  exact valueEquality

/-- Original module morphisms are small through their specified injective section encoding. -/
theorem locallySmall : LocallySmall.{u} X.Modules where
  hom_small M N := small_of_injective (sectionFunctions_injective X M N)

/-- Filtered sheaf colimits are exact in the original module universe. -/
theorem ab5 : AB5OfSize.{u, u} X.Modules := by
  letI : (PresheafOfModules.toPresheaf (structureSheaf X).obj).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms _
  letI : ReflectsFiniteLimits (PresheafOfModules.toPresheaf (structureSheaf X).obj) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms _
  letI : AB5OfSize.{u, u} (PresheafOfModules.{u} (structureSheaf X).obj) :=
    ⟨fun diagramShape _ _ ↦ HasExactColimitsOfShape.domain_of_functor diagramShape
      (PresheafOfModules.toPresheaf (structureSheaf X).obj)⟩
  exact ⟨fun diagramShape _ _ ↦
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (structureSheaf X).obj)).hasExactColimitsOfShape
      diagramShape⟩

end AlgebraicGeometry.AlgebraicSpace.Modules.AtlasGenerator

namespace AlgebraicGeometry.AlgebraicSpace

/-- Original-universe module sheaves form a Grothendieck category with the specified
small-atlas generator and the actual sheaf colimits. -/
instance modulesIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian.{u} X.Modules where
  locallySmall := Modules.AtlasGenerator.locallySmall X
  hasFilteredColimitsOfSize := inferInstance
  ab5OfSize := Modules.AtlasGenerator.ab5 X
  hasSeparator := ⟨Modules.AtlasGenerator.generator X, Modules.AtlasGenerator.generator_isSeparator X⟩

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- The category of quasi-coherent modules on an algebraic space is Grothendieck abelian. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsGrothendieckAbelian (QCoh X) :=
  sorry

/-- The inclusion of quasi-coherent modules into all module sheaves has a right adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.QCoh
