module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived comparison after forgetting module structure

@stack 0D6J

This module owns the reusable comparison from derived module sections to derived sections of the
underlying additive sheaf.  The source-facing statement is split into homotopy models, units, the
canonical comparison morphism, and its isomorphism companions so downstream files can reuse the
actual morphism rather than reconstructing a private chapter proof.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape Opposite

noncomputable section

-- Local instance justification (defeq pin): use the standard derived-category model
-- already fixed explicitly by ModuleDerived and moduleLocalization.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe z u v w

namespace RingedSite.Hom.ModuleSections

open Underlying

variable (X : RingedSite.{u, v, w})
variable [UnivLE.{max u v, z}]
variable [HasSheafify X.siteTopology AddCommGrpCat.{z}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{z}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{z}]
variable [Functor.HasRightDerivedFunctor
  (moduleGlobalSectionsToDerived.{z} X) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor (globalToDerived X)
  (HomotopyCategory.quasiIso
    (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))]

/-- The homotopy-level source of the global forgetful comparison. -/
@[stacks 0D6J "global forgetful source"]
noncomputable abbrev globalSource :
    HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  moduleGlobalSectionsToDerived.{z} X

/-- The homotopy-level target of the global forgetful comparison. -/
@[stacks 0D6J "global forgetful target"]
noncomputable abbrev globalTarget :
    HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
    globalToDerived X

/-- The derived source of the global forgetful comparison. -/
@[stacks 0D6J "derived global forgetful source"]
noncomputable abbrev globalSourceDerived :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  Functor.totalRightDerived (moduleGlobalSectionsToDerived.{z} X)
    (moduleLocalization.{z} X) (ModuleQis.{z} X)

/-- The derived target of the global forgetful comparison. -/
@[stacks 0D6J "derived global forgetful target"]
noncomputable abbrev globalTargetDerived :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory ⋙
    globalDerived X

/-- The canonical right-derived unit for the global forgetful source. -/
@[stacks 0D6J "global forgetful source unit"]
noncomputable def globalSourceUnit :
    globalSource X ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X) ⋙
        globalSourceDerived X :=
  Functor.totalRightDerivedUnit
    (moduleGlobalSectionsToDerived.{z} X)
    (DerivedCategory.Qh :
      HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
    (ModuleQis.{z} X)

/-- The canonical right-derived unit for the additive homotopy target. -/
@[stacks 0D6J "global forgetful target unit"]
noncomputable def globalTargetUnit :
    globalTarget X ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X) ⋙
        globalTargetDerived X :=
  Functor.whiskerLeft
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (Functor.totalRightDerivedUnit
        (globalToDerived X)
        (DerivedCategory.Qh :
          HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
            DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
        (HomotopyCategory.quasiIso
          (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ))) ≫
    (Functor.associator
      ((underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh :
        HomotopyCategory (Sheaf X.siteTopology AddCommGrpCat.{z}) (up ℤ) ⥤
          DerivedCategory (Sheaf X.siteTopology AddCommGrpCat.{z}))
      (globalDerived X)).inv ≫
    Functor.whiskerRight
      ((underlyingAbelianSheafFunctor.{z} X).mapDerivedCategoryFactorsh.inv :
        (underlyingAbelianSheafFunctor.{z} X).mapHomotopyCategory (up ℤ) ⋙
            DerivedCategory.Qh ⟶
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X) ⋙
            (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory)
      (globalDerived X) ≫
    (Functor.associator
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
      (underlyingAbelianSheafFunctor.{z} X).mapDerivedCategory
      (globalDerived X)).hom

/-- The global derived target is equipped with its canonical right-derived-functor witness. -/
@[stacks 0D6J "global forgetful target model"]
noncomputable instance globalTarget_isRightDerived :
    (globalTargetDerived X).IsRightDerivedFunctor
      (globalTargetUnit X) (ModuleQis.{z} X) := sorry

/-- The global derived source is equipped with its canonical right-derived-functor witness. -/
@[stacks 0D6J "global forgetful source model"]
noncomputable instance globalSource_isRightDerived :
    (globalSourceDerived X).IsRightDerivedFunctor
      (globalSourceUnit X) (ModuleQis.{z} X) := sorry

/-- The derived global forgetful comparison as a reusable natural isomorphism. -/
@[stacks 0D6J "derived global forgetful comparison isomorphism"]
noncomputable def globalIso :
    globalSourceDerived X ≅ globalTargetDerived X :=
  Functor.rightDerivedNatIso
    (globalSourceDerived X) (globalTargetDerived X)
    (globalSourceUnit X) (globalTargetUnit X)
    (ModuleQis.{z} X)
    (globalCompIso X)

/-- The forward morphism of the derived global forgetful isomorphism. -/
@[stacks 0D6J "derived global forgetful comparison"]
noncomputable abbrev globalComparison :
    globalSourceDerived X ⟶ globalTargetDerived X :=
  (globalIso X).hom

/-- The global comparison satisfies the right-derived universal-property equation. -/
@[stacks 0D6J "global derived comparison factorization", reassoc (attr := simp)]
lemma globalComparison_fac :
    globalSourceUnit X ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (globalComparison X) =
      (globalCompIso X).hom ≫
        globalTargetUnit X := sorry

/-- The global comparison factorization equation at a homotopy object. -/
@[stacks 0D6J "global derived comparison factorization component"]
theorem globalComparison_fac_app
    (M : HomotopyCategory (ModuleCat.{z} X) (up ℤ)) :
    (globalSourceUnit X).app M ≫
        (globalComparison X).app
          ((DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (globalCompIso X).hom.app M ≫
        (globalTargetUnit X).app M := sorry

/-- The inverse global comparison satisfies the reverse right-derived factorization equation. -/
@[stacks 0D6J "global derived comparison reverse factorization", reassoc (attr := simp)]
lemma globalComparison_inv_fac :
    globalTargetUnit X ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (globalIso X).inv =
      (globalCompIso X).inv ≫
        globalSourceUnit X := sorry

/-- The reverse global comparison factorization at a homotopy object. -/
@[stacks 0D6J "global derived comparison reverse factorization component"]
theorem globalComparison_inv_fac_app
    (M : HomotopyCategory (ModuleCat.{z} X) (up ℤ)) :
    (globalTargetUnit X).app M ≫
        (globalIso X).inv.app
          ((DerivedCategory.Qh :
            HomotopyCategory (ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (globalCompIso X).inv.app M ≫
        (globalSourceUnit X).app M := sorry

/-- The homotopy-level global bridge at one module complex. -/
@[stacks 0D6J "global homotopy bridge component"]
noncomputable abbrev globalHomotopyAppIso
    (M : HomotopyCategory (ModuleCat.{z} X) (up ℤ)) :
    (globalSource X).obj M ≅ (globalTarget X).obj M :=
  (globalCompIso X).app M

/-- The derived global forgetful comparison at a module complex. -/
@[stacks 0D6J "derived global forgetful comparison component"]
noncomputable abbrev globalAppIso (K : ModuleDerived.{z} X) :
    (globalSourceDerived X).obj K ≅ (globalTargetDerived X).obj K :=
  (globalIso X).app K

end RingedSite.Hom.ModuleSections
