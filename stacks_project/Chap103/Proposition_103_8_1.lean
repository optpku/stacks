/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Properties
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Pullback
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Comparison
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import stacks_project.Chap96.Lemma_96_12_4
public import stacks_project.Chap103.Lemma_103_7_2
public import stacks_project.Chap103.Lemma_103_7_3
public import stacks_project.Chap104.Definition_104_5_1_LQCohFbc
public import stacks_project.Chap103.Proposition_103_8_1_FppfSheaf
import StacksCheckRecall

/-! # Locally quasi-coherent modules with flat base change

The seven stability and topology-comparison assertions for algebraic stacks.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidsOver CategoryTheory.ObjectProperty
open scoped Bicategory

universe u v w

/- Proposition 103.8.1 (4)(a): higher direct images agree after restricting the
actual enlarged fppf higher direct image to the enlarged étale category. -/
@[stacks 0771] #check
  (AlgebraicGeometry.GroupoidsOver.higherDirectImage_etale_iso_fppf :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
      (F : LQCohFbc X) (i : ℕ),
      IsIsomorphic
        ((AlgebraicStack.liftedFppfToEtale Y).obj
          ((fppfHigherDirectImageLiftFunctor f i).obj
            ((fppfModuleUniverseLift X).obj ((LQCohFbc.toFppf X).obj F))))
        (moduleHigherDirectImage f F.obj i))

/- Proposition 103.8.1 (1): locally quasi-coherent modules with flat base change
are fppf sheaves. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.isSheaf_fppf_of_lqcohFbc :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F],
    Presheaf.IsSheaf (ringedSite X).siteTopology (etaleModulePresheaf F).presheaf)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toFppf :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    LQCohFbc X ⥤ fppfModules X)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toFppf_obj_val :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] (F : LQCohFbc X),
    ((LQCohFbc.toFppf X).obj F).val = etaleModulePresheaf F.obj)

/- Proposition 103.8.1 (2): both ambient module categories contain the indicated
weak Serre subcategory. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.lqcohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (lqcohFbc X))

#check (AlgebraicGeometry.GroupoidsOver.FppfModules.lqcohFbc_isWeakSerreClass :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsWeakSerreClass (FppfModules.lqcohFbc X))

/- Proposition 103.8.1 (3): arbitrary pullback preserves the subcategory. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.inverseImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), LQCohFbc Y ⥤ LQCohFbc X)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.inverseImage_comp_inclusion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y), LQCohFbc.inverseImage f ⋙ LQCohFbc.inclusion X =
      LQCohFbc.inclusion Y ⋙ etaleModuleInverseImage f)

/- Proposition 103.8.1 (4)(a): total direct images agree on degree-zero inputs,
using actual derived direct image and derived topology restriction. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.derivedPushforward_etale_iso_fppf :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X),
    IsIsomorphic
      (DerivedCategory.Plus.ι.obj
        ((AlgebraicStack.liftedFppfToEtale Y).rightDerivedFunctorPlus.obj
          ((fppfDerivedDirectImageLiftFunctor f).obj
            ((DerivedCategory.Plus.singleFunctor
              (RingedSite.ModuleCat.{u + 1} (liftedFppfRingedSite X)) (0 : ℤ)).obj
                ((fppfModuleUniverseLift X).obj ((LQCohFbc.toFppf X).obj F))))))
      (DerivedCategory.Plus.ι.obj
        ((etaleDerivedDirectImageLiftFunctor f).obj
          ((DerivedCategory.Plus.singleFunctor (EtaleModulesLift X) (0 : ℤ)).obj
            ((ModuleUniverseComparison.lift X).obj F.obj)))))

/- Proposition 103.8.1 (4)(b): higher direct images remain in the enlarged
locally quasi-coherent flat-base-change class. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.mem_lqcohFbc_higherDirectImage :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    (F : LQCohFbc X) (i : ℕ),
    AlgebraicStack.liftedEtaleLqcohFbc Y (moduleHigherDirectImage f F.obj i))

/- Proposition 103.8.1 (5): colimits exist and agree with both ambient colimits. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.closedUnderColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J], (lqcohFbc X).IsClosedUnderColimitsOfShape J)

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.toFppf_preservesColimitsOfShape :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}],
    PreservesColimitsOfShape J (LQCohFbc.toFppf X))

section Colimits

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
  (J : Type v) [Category.{w} J] [HasColimitsOfShape J AddCommGrpCat.{u}]

#check (CategoryTheory.Limits.createsColimitsOfShapeFullSubcategoryInclusion
  J (lqcohFbc X) : CreatesColimitsOfShape J (LQCohFbc.inclusion X))

#check (CategoryTheory.Limits.hasColimitsOfShape_of_closedUnderColimits
  J (lqcohFbc X) : HasColimitsOfShape J (LQCohFbc X))

variable (F : J ⥤ LQCohFbc X)

#check (CategoryTheory.preservesColimitIso (LQCohFbc.inclusion X) F :
  (LQCohFbc.inclusion X).obj (colimit F) ≅ colimit (F ⋙ LQCohFbc.inclusion X))

#check (CategoryTheory.preservesColimitIso (LQCohFbc.toFppf X) F :
  (LQCohFbc.toFppf X).obj (colimit F) ≅ colimit (F ⋙ LQCohFbc.toFppf X))

end Colimits

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.colimit_isSheaf_fppf :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {J : Type v} [Category.{w} J] (F : J ⥤ LQCohFbc X) [HasColimit F],
    Presheaf.IsSheaf (ringedSite X).siteTopology
      (etaleModulePresheaf ((LQCohFbc.inclusion X).obj (colimit F))).presheaf)

/- Proposition 103.8.1 (6): the ambient tensor product remains in the subcategory. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.tensor_obj :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] (F G : LQCohFbc X),
    (LQCohFbc.tensor F G).obj = moduleTensorEtale F.obj G.obj)

/- Proposition 103.8.1 (7): internal Hom from any finitely presented module
into a module in the subcategory remains in the subcategory. -/
@[stacks 0771] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.mem_sheafHom :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X),
    lqcohFbc X (moduleSheafHomEtale F G.obj))

#check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.sheafHom_obj :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [F.IsFinitePresentation] (G : LQCohFbc X),
    (LQCohFbc.sheafHom F G).obj = moduleSheafHomEtale F G.obj)
