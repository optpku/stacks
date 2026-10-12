/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived objectwise comparison after forgetting module structure

This module owns the comparison between sections over an object followed by the derived forgetful
functor and the derived sections of the underlying additive sheaf.  The source and target models,
their units, and the canonical comparison are public so later cohomology statements can reuse the
same morphism.
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

variable (X : RingedSite.{u, v, w}) (U : X)
variable [UnivLE.{max u v, z}]
variable [Functor.HasRightDerivedFunctor
  (moduleSectionsToDerived.{z} X U) (ModuleQis.{z} X)]
variable [Functor.HasRightDerivedFunctor
  (sectionsToDerived X U) (ModuleQis.{z} X)]

/-- The homotopy-level source for the objectwise forgetful comparison. -/
@[stacks 0D6J "objectwise forgetful source"]
noncomputable abbrev sectionsSource :
    HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  moduleSectionsToDerived.{z} X U ⋙
    (sectionForget X U).mapDerivedCategory

/-- The homotopy-level target for the objectwise forgetful comparison. -/
@[stacks 0D6J "objectwise forgetful target"]
noncomputable abbrev sectionsTarget :
    HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
      DerivedCategory AddCommGrpCat.{z} :=
  sectionsToDerived X U

/-- The derived source for the objectwise forgetful comparison. -/
@[stacks 0D6J "derived objectwise forgetful source"]
noncomputable abbrev sectionsSourceDerived :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  Functor.totalRightDerived (moduleSectionsToDerived.{z} X U)
      (moduleLocalization.{z} X) (ModuleQis.{z} X) ⋙
    (sectionForget X U).mapDerivedCategory

/-- The derived target for the objectwise forgetful comparison. -/
@[stacks 0D6J "derived objectwise forgetful target"]
noncomputable abbrev sectionsTargetDerived :
    ModuleDerived.{z} X ⥤ DerivedCategory AddCommGrpCat.{z} :=
  Functor.totalRightDerived (sectionsToDerived.{z} X U)
    (moduleLocalization.{z} X) (ModuleQis.{z} X)

/-- The canonical right-derived unit for the objectwise source. -/
@[stacks 0D6J "objectwise forgetful source unit"]
noncomputable def sectionsSourceUnit :
    sectionsSource X U ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X) ⋙ sectionsSourceDerived X U :=
  Functor.whiskerRight
      (Functor.totalRightDerivedUnit
        (moduleSectionsToDerived.{z} X U)
        (DerivedCategory.Qh :
          HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
            ModuleDerived.{z} X)
        (ModuleQis.{z} X))
      (sectionForget X U).mapDerivedCategory ≫
    (Functor.associator
      (DerivedCategory.Qh :
      HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X)
      (Functor.totalRightDerived (moduleSectionsToDerived.{z} X U)
        (moduleLocalization.{z} X) (ModuleQis.{z} X))
      (sectionForget X U).mapDerivedCategory).hom

/-- The canonical right-derived unit for the objectwise target. -/
@[stacks 0D6J "objectwise forgetful target unit"]
noncomputable def sectionsTargetUnit :
    sectionsTarget X U ⟶
      (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X) ⋙ sectionsTargetDerived X U :=
  Functor.totalRightDerivedUnit
    (sectionsToDerived X U)
    (DerivedCategory.Qh :
        HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤
          ModuleDerived.{z} X)
    (ModuleQis.{z} X)

/-- The objectwise source is equipped with its right-derived-functor witness. -/
@[stacks 0D6J "objectwise forgetful source model"]
noncomputable instance sectionsSource_isRightDerived :
    (sectionsSourceDerived X U).IsRightDerivedFunctor
      (sectionsSourceUnit X U) (ModuleQis.{z} X) := sorry

/-- The objectwise target is equipped with its right-derived-functor witness. -/
@[stacks 0D6J "objectwise forgetful target model"]
noncomputable instance sectionsTarget_isRightDerived :
    (sectionsTargetDerived X U).IsRightDerivedFunctor
      (sectionsTargetUnit X U) (ModuleQis.{z} X) := sorry

/-- The objectwise forgetful comparison as a reusable natural isomorphism. -/
@[stacks 0D6J "derived objectwise forgetful comparison isomorphism"]
noncomputable def sectionsIso :
    sectionsSourceDerived X U ≅ sectionsTargetDerived X U :=
  Functor.rightDerivedNatIso
    (sectionsSourceDerived X U) (sectionsTargetDerived X U)
    (sectionsSourceUnit X U) (sectionsTargetUnit X U)
    (ModuleQis.{z} X)
    (sectionsCompIso X U).symm

/-- The forward morphism of the objectwise derived forgetful isomorphism. -/
@[stacks 0D6J "derived objectwise forgetful comparison"]
noncomputable abbrev sectionsComparison :
    sectionsSourceDerived X U ⟶ sectionsTargetDerived X U :=
  (sectionsIso X U).hom

/-- The objectwise comparison satisfies the right-derived universal-property equation. -/
@[stacks 0D6J "objectwise derived comparison factorization", reassoc (attr := simp)]
lemma sectionsComparison_fac :
    sectionsSourceUnit X U ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (sectionsComparison X U) =
      (sectionsCompIso X U).symm.hom ≫
        sectionsTargetUnit X U := sorry

/-- The objectwise comparison factorization equation at a homotopy object. -/
@[stacks 0D6J "objectwise derived comparison factorization component"]
lemma sectionsComparison_fac_app
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (sectionsSourceUnit X U).app M ≫
        (sectionsComparison X U).app
          ((DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (sectionsCompIso X U).symm.hom.app M ≫
        (sectionsTargetUnit X U).app M := sorry

/-- The inverse objectwise comparison satisfies the reverse right-derived factorization equation. -/
@[stacks 0D6J "objectwise derived comparison reverse factorization", reassoc (attr := simp)]
lemma sectionsComparison_inv_fac :
    sectionsTargetUnit X U ≫
        Functor.whiskerLeft
          (DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X)
          (sectionsIso X U).inv =
      (sectionsCompIso X U).hom ≫
        sectionsSourceUnit X U := sorry

/-- The reverse objectwise comparison factorization at a homotopy object. -/
@[stacks 0D6J "objectwise derived comparison reverse factorization component"]
lemma sectionsComparison_inv_fac_app
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (sectionsTargetUnit X U).app M ≫
        (sectionsIso X U).inv.app
          ((DerivedCategory.Qh :
            HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ) ⥤ ModuleDerived.{z} X).obj M) =
      (sectionsCompIso X U).hom.app M ≫
        (sectionsSourceUnit X U).app M := sorry

/-- The homotopy-level objectwise bridge at one module complex, oriented from source to target. -/
@[stacks 0D6J "objectwise homotopy bridge component"]
noncomputable abbrev sectionsHomotopyAppIso
    (M : HomotopyCategory (RingedSite.ModuleCat.{z} X) (up ℤ)) :
    (sectionsSource X U).obj M ≅ (sectionsTarget X U).obj M :=
  (sectionsCompIso X U).symm.app M

/-- The objectwise derived forgetful comparison at a module complex. -/
@[stacks 0D6J "derived objectwise forgetful comparison component"]
noncomputable abbrev sectionsAppIso (K : ModuleDerived.{z} X) :
    (sectionsSourceDerived X U).obj K ≅ (sectionsTargetDerived X U).obj K :=
  (sectionsIso X U).app K

end RingedSite.Hom.ModuleSections
