/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Homotopy
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Injective Total Right Derived Functors

This file specializes the construction-neutral homotopy API to a Grothendieck-abelian source,
where K-injective resolutions supply the required total right-derived instance.  Import
`TotalRightDerived.Homotopy` when a derived-functor instance is already available.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w wA wB uA uB vA vB

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wB} B]

/-- The proposition that the homotopy-to-derived functor of `F` admits a total right derived
functor. This is a transparent specialization of Mathlib's `Functor.HasRightDerivedFunctor`. -/
@[stacks 05TH]
abbrev Functor.RightDerived.KInjective.HasDerived (F : A ⥤ B) [F.Additive] : Prop :=
  (Functor.Homotopy.toDerived F).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (up ℤ))

/-- K-injective resolutions give a right derived functor for the homotopy-to-derived functor
associated to an additive functor with Grothendieck-abelian source. -/
@[stacks 05TH]
instance Functor.RightDerived.KInjective.hasDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    Functor.RightDerived.KInjective.HasDerived F := by
  letI := HasDerivedCategory.standard A
  exact Functor.KInjectiveModel.Homotopy.hasRightDerived F

/-- The K-injective specialization of the total right derived functor. -/
@[stacks 05TH]
abbrev Functor.RightDerived.KInjective.functor
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [Functor.RightDerived.KInjective.HasDerived F] :
    DerivedCategory A ⥤ DerivedCategory B :=
  Functor.RightDerived.Homotopy.functor F

/-- The cochain-level comparison unit for the K-injective total right derived functor. -/
@[stacks 05TH]
noncomputable abbrev Functor.RightDerived.KInjective.unit
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [Functor.RightDerived.KInjective.HasDerived F] :
    F.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) ⟶
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        Functor.RightDerived.KInjective.functor F :=
  Functor.RightDerived.Homotopy.cochainUnit F

namespace Functor.RightDerived.Homotopy

/-- A cochain comparison descends through the homotopy quotient after the native
factorization isomorphisms change its source and target presentations. -/
def cochainExtensionHomotopy (F : A ⥤ B) [F.Additive]
    (G : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G) :
    Functor.Homotopy.toDerived F ⟶ DerivedCategory.Qh ⋙ G :=
  CategoryTheory.Quotient.natTransLift _
    ((Functor.Homotopy.cochainIso F).hom ≫ β ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) G).inv ≫
      (Functor.associator _ _ _).hom)

/-- The cochain extension map is the caller's chosen homotopy-derived universal map,
with its comparison descended through the quotient. -/
def cochainExtensionDesc (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (G : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G) :
    functor F ⟶ G := by
  letI hNative : (functor F).IsRightDerivedFunctor (unit F)
      (HomotopyCategory.quasiIso A (up ℤ)) :=
    Functor.instIsRightDerivedFunctorTotalRightDerivedTotalRightDerivedUnit
      (Functor.Homotopy.toDerived F) (DerivedCategory.Qh (C := A))
      (HomotopyCategory.quasiIso A (up ℤ))
  exact (functor F).rightDerivedDesc (unit F)
    (HomotopyCategory.quasiIso A (up ℤ)) G (cochainExtensionHomotopy F G β)

/-- The cochain extension map has the required comparison with the given cochain unit. -/
theorem cochainExtensionDesc_fac (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (G : DerivedCategory A ⥤ DerivedCategory B)
    (β : F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ G) :
    cochainUnit F ≫ Functor.whiskerLeft DerivedCategory.Q (cochainExtensionDesc F G β) = β :=
  sorry

/-- The actual cochain left-extension arrow uses that chosen universal map. -/
def cochainInitialExtensionDesc (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (E : Functor.LeftExtension (DerivedCategory.Q (C := A))
      (F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q (C := B))) :
    Functor.LeftExtension.mk (functor F) (cochainUnit F) ⟶ E :=
  StructuredArrow.homMk (cochainExtensionDesc F E.right E.hom)
    (cochainExtensionDesc_fac F E.right E.hom)

/-- Quotient descent and the caller's homotopy-derived uniqueness determine this arrow. -/
theorem cochainInitialExtensionDesc_unique (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (E : Functor.LeftExtension (DerivedCategory.Q (C := A))
      (F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q (C := B)))
    (m : Functor.LeftExtension.mk (functor F) (cochainUnit F) ⟶ E) :
    m = cochainInitialExtensionDesc F E := sorry

/-- The cochain universal witness retains the caller's chosen homotopy-derived model. -/
def cochainInitialWitness (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (Functor.LeftExtension.mk (functor F) (cochainUnit F)).IsUniversal :=
  CategoryTheory.Limits.IsInitial.ofUniqueHom
    (cochainInitialExtensionDesc F) (cochainInitialExtensionDesc_unique F)

end Functor.RightDerived.Homotopy

namespace Functor.RightDerived.KInjective

/-- The K-injective cochain comparison exhibits the specialization as a right derived functor. -/
@[stacks 05TH]
theorem isRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [Functor.RightDerived.KInjective.HasDerived F] :
    (Functor.RightDerived.KInjective.functor F).IsRightDerivedFunctor
      (Functor.RightDerived.KInjective.unit F)
      (HomologicalComplex.quasiIso A (up ℤ)) where
  isLeftKanExtension :=
    { nonempty_isUniversal := ⟨Functor.RightDerived.Homotopy.cochainInitialWitness F⟩ }

end Functor.RightDerived.KInjective

/-- The cochain-level functor induced by an additive functor admits the canonical total right
derived functor obtained through K-injective resolutions. -/
@[stacks 05TH]
instance Functor.RightDerived.Cochain.hasDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (Functor.RightDerived.Cochain.toDerived F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) := by
  letI := HasDerivedCategory.standard A
  exact Functor.KInjectiveModel.hasRightDerived F



end CategoryTheory
