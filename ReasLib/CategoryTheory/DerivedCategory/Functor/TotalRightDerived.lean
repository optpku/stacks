/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

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
    Functor.RightDerived.KInjective.HasDerived F := sorry

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

namespace Functor.RightDerived.KInjective

/-- The K-injective cochain comparison exhibits the specialization as a right derived functor. -/
@[stacks 05TH]
theorem isRightDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A]
    [Functor.RightDerived.KInjective.HasDerived F] :
    (Functor.RightDerived.KInjective.functor F).IsRightDerivedFunctor
      (Functor.RightDerived.KInjective.unit F)
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

end Functor.RightDerived.KInjective

/-- The cochain-level functor induced by an additive functor admits the canonical total right
derived functor obtained through K-injective resolutions. -/
@[stacks 05TH]
instance Functor.RightDerived.Cochain.hasDerived
    (F : A ⥤ B) [F.Additive] [IsGrothendieckAbelian.{w} A] :
    (Functor.RightDerived.Cochain.toDerived F).HasRightDerivedFunctor
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry



end CategoryTheory
