/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap52.Lemma_52_6_1
public import stacks_project.Chap52.Lemma_52_6_11
public import stacks_project.Chap52.«52_7_0_1_Completion»
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.CategoryTheory.Monoidal.Closed.Functoriality
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CechCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite SheafOfModules.RingedSite.ExtendedCech

noncomputable section

universe u

namespace RingedSite.Hom.ModuleDerived
namespace CechCompletion

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [J.WEqualsLocallyBijective CommRingCat.{u}]
variable {O : Sheaf J CommRingCat.{u}}

section Compatibility

variable [MonoidalCategory (RingedSiteDerived J O)]

/-- The value of the supplied closed structure's internal Hom from the Čech object.
This compatibility surface does not assert that the value is a derived completion. -/
noncomputable abbrev obj {r : ℕ}
    (H : MonoidalClosed (RingedSiteDerived J O))
    (f : Fin r → (unitModule J O).sections) (K : RingedSiteDerived J O) :
    RingedSiteDerived J O :=
  (MonoidalClosed.ihomOf H (ExtendedCech.derived f)).obj K

end Compatibility

/- Lemma 52.6.8: a finitely globally generated ideal sheaf admits universal derived
completion, functorially computed by sheaf internal Hom from the extended alternating Čech
complex. -/
@[stacks 099B] #check
  (RingedSite.Hom.ModuleDerived.CechCompletion.existsDerivedCompletion :
    ∀ {r : ℕ} (I : Subobject (unitModule J O))
      (f : Fin r → (unitModule J O).sections) (hgen : generatedIdeal f = I),
      ∃ R : ObjectProperty.Reflector (derivedCompleteObjectProperty.{u, u, u, u} I),
        ∃ alpha : sheafHomComplexFunctor
            ((ExtendedCech.complex f).extend ComplexShape.embeddingUpNat) ⟶
              DerivedCategory.Q ⋙ R.reflection,
          R.reflection.IsRightDerivedFunctor alpha
              (HomologicalComplex.quasiIso (ringedSiteModuleCategory J O) (ComplexShape.up ℤ)) ∧
            (∀ K : RingedSiteDerived J O, IsDerivedCompletion.{u, u, u, u} I (R.unit.app K)) ∧
            (∀ (X : CochainComplex (ringedSiteModuleCategory J O) ℤ) [X.IsKInjective],
              IsIso (alpha.app X)))

end CechCompletion
end RingedSite.Hom.ModuleDerived
