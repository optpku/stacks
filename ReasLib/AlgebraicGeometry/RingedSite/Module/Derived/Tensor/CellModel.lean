/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CellReplacement.Functorial
public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.CategoryTheory.Functor.Derived.Deformation
public import ReasLib.CategoryTheory.Localization.FormalIso
public import Mathlib.CategoryTheory.Localization.Prod

/-! # Derived tensor from functorial cell complexes -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace RingedSite.NativeDerived.CellTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/-- Cochain complexes of modules over the commutative coefficient sheaf. -/
abbrev Complex := CochainComplex (ModuleCat.{w} (ofCommRingSheaf J O)) ℤ

/-- Localization of module complexes into the native standard derived category. -/
abbrev Q : Complex O ⥤ category.{w} (ofCommRingSheaf J O) :=
  @DerivedCategory.Q _ _ (abelian.{w} (ofCommRingSheaf J O))
    (hasDerivedCategory.{w} (ofCommRingSheaf J O))

/-- Quasi-isomorphisms of module complexes. -/
abbrev quasiIso : MorphismProperty (Complex O) :=
  HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)

/-- The native standard derived localization inverts exactly the module quasi-isomorphisms. -/
instance qIsLocalization : (Q O).IsLocalization (quasiIso O) := inferInstance

/-- The actual functorial cell replacement of a module complex. -/
abbrev replacement : Complex O ⥤ Complex O := SheafOfModules.CellReplacement.functor

/-- The original augmentation of the cell replacement. -/
abbrev augmentation : replacement O ⟶ 𝟭 (Complex O) :=
  SheafOfModules.CellReplacement.augmentationNatTrans

/-- Ordinary tensor totalization of two module complexes. -/
def tensorComplex : Complex O × Complex O ⥤ Complex O :=
  Functor.uncurry.obj ((curriedTensor (ModuleCat.{w} (ofCommRingSheaf J O))).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor _ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- Total tensor product of the two actual cell replacement complexes. -/
def cochain : Complex O × Complex O ⥤ Complex O :=
  ((replacement O).prod (replacement O)) ⋙ tensorComplex O

/-- Localized tensor of cell replacements inverts pairs of quasi-isomorphisms. -/
theorem invertsQuasiIso :
    ((quasiIso O).prod (quasiIso O)).IsInvertedBy (cochain O ⋙ Q O) := sorry

/-- Derived tensor obtained by localizing total tensor of actual cell replacements. -/
def functor : category.{w} (ofCommRingSheaf J O) ×
    category.{w} (ofCommRingSheaf J O) ⥤ category.{w} (ofCommRingSheaf J O) :=
  Localization.lift (cochain O ⋙ Q O) (invertsQuasiIso O) ((Q O).prod (Q O))

/-- On original complexes, derived tensor is the localized tensor of their cell replacements. -/
def computation : ((Q O).prod (Q O)) ⋙ functor O ≅ cochain O ⋙ Q O :=
  Localization.fac (cochain O ⋙ Q O) (invertsQuasiIso O) ((Q O).prod (Q O))

/-- Augmenting the left tensor factor is a quasi-isomorphism when the other factor is K-flat. -/
theorem augmentationLeft_quasiIso (K L : Complex O) (hL : L.IsKFlat) :
    QuasiIso (HomologicalComplex.tensorHom ((augmentation O).app K) (𝟙 L)) := sorry

/-- Augmenting the right tensor factor is a quasi-isomorphism when the other factor is K-flat. -/
theorem augmentationRight_quasiIso (K L : Complex O) (hK : K.IsKFlat) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 K) ((augmentation O).app L)) := sorry

/-- The derived tensor counit is induced by the two original cell augmentations. -/
def counit : ((Q O).prod (Q O)) ⋙ functor O ⟶ tensorComplex O ⋙ Q O :=
  Functor.LeftDerived.Deformation.counit ((Q O).prod (Q O))
    ((replacement O).prod (replacement O)) ((augmentation O).prod (augmentation O))
    (tensorComplex O ⋙ Q O) (functor O) (computation O)

/-- The augmented cell tensor model, with its specified augmentation-based universal extension maps. -/
def derivedModel : Functor.LeftDerived.Model (tensorComplex O ⋙ Q O)
    ((Q O).prod (Q O)) ((quasiIso O).prod (quasiIso O)) :=
  let F := tensorComplex O ⋙ Q O
  let hAug := fun P : Complex O × Complex O ↦
    let K := (replacement O).obj P.1
    let L := (replacement O).obj P.2
    let a := (augmentation O).app K
    let b := (augmentation O).app L
    let f : (((replacement O).obj K), ((replacement O).obj L)) ⟶
        (K, ((replacement O).obj L)) := (a, 𝟙 _)
    let g : (K, ((replacement O).obj L)) ⟶ (K, L) := (𝟙 _, b)
    let heq : F.map (a, b) = F.map f ≫ F.map g :=
      (congrArg F.map (CategoryTheory.Prod.hom_ext (Category.comp_id a)
        (Category.id_comp b))).symm.trans (F.map_comp f g)
    Eq.mpr (congrArg IsIso heq)
      (IsIso.comp_isIso'
        (Localization.inverts (Q O) (quasiIso O) _
          (augmentationLeft_quasiIso O K ((replacement O).obj L)
            (SheafOfModules.RingedSite.CellReplacement.model_isKFlat L)))
        (Localization.inverts (Q O) (quasiIso O) _
          (augmentationRight_quasiIso O K L
            (SheafOfModules.RingedSite.CellReplacement.model_isKFlat P.1))))
  ⟨functor O, counit O,
    Functor.LeftDerived.Deformation.isLeftDerived ((Q O).prod (Q O))
      ((quasiIso O).prod (quasiIso O)) ((replacement O).prod (replacement O))
      ((augmentation O).prod (augmentation O))
      (fun P ↦ ⟨SheafOfModules.CellReplacement.augmentation_quasiIso P.1,
        SheafOfModules.CellReplacement.augmentation_quasiIso P.2⟩)
      F (functor O) (computation O) hAug⟩

end RingedSite.NativeDerived.CellTensor
