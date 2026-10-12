/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Cochain Comparison for Homotopy-to-Derived Functors

This file compares the homotopy-to-derived functor after the homotopy quotient with direct
termwise application followed by derived localization.  The comparison is variance-neutral and
is shared by total right and left derived functors.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe uA vA uB vB

namespace CategoryTheory.Functor.Homotopy

variable {A : Type uA} [Category.{vA} A] [Preadditive A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]

/-- Applying an additive functor after the homotopy quotient agrees with applying it termwise
and then localizing the resulting cochain complex. -/
@[stacks 05S3]
noncomputable def cochainIso (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.quotient A (up ℤ) ⋙ Homotopy.toDerived F ≅
      F.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) :=
  (Functor.associator
      (HomotopyCategory.quotient A (up ℤ))
      (F.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryFactors F (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B) ≪≫
    Functor.associator
      (F.mapHomologicalComplex (up ℤ))
      (HomotopyCategory.quotient B (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B) ≪≫
    Functor.isoWhiskerLeft
      (F.mapHomologicalComplex (up ℤ))
      (DerivedCategory.quotientCompQhIso B)

variable [HasZeroObject A]

/-- Applying an additive functor to a single object in the homotopy category
and then localizing agrees with the corresponding single object in the target
derived category. -/
@[stacks 015A]
noncomputable def singleIso (F : A ⥤ B) [F.Additive] (n : ℤ) :
    HomotopyCategory.singleFunctor A n ⋙ Homotopy.toDerived F ≅
      F ⋙ DerivedCategory.singleFunctor B n :=
  Functor.isoWhiskerRight
      (HomotopyCategory.singleFunctorPostcompQuotientIso A n)
      (Homotopy.toDerived F) ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (CochainComplex.singleFunctor A n)
        (cochainIso F) ≪≫
        (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (HomologicalComplex.singleMapHomologicalComplex
              F (ComplexShape.up ℤ) n)
            DerivedCategory.Q ≪≫
          Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft F
              (DerivedCategory.singleFunctorIsoCompQ B n).symm

namespace singleIso

/-- Naturality of the forward homotopy-to-derived single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "single-object comparison naturality"]
theorem hom_naturality (F : A ⥤ B) [F.Additive] (n : ℤ)
    {X Y : A} (f : X ⟶ Y) :
    (HomotopyCategory.singleFunctor A n ⋙ Homotopy.toDerived F).map f ≫
        (singleIso F n).hom.app Y =
      (singleIso F n).hom.app X ≫
        (F ⋙ DerivedCategory.singleFunctor B n).map f := sorry

/-- Naturality of the inverse homotopy-to-derived single-object comparison. -/
@[reassoc (attr := simp), stacks 015A "single-object comparison naturality"]
theorem inv_naturality (F : A ⥤ B) [F.Additive] (n : ℤ)
    {X Y : A} (f : X ⟶ Y) :
    (F ⋙ DerivedCategory.singleFunctor B n).map f ≫
        (singleIso F n).inv.app Y =
      (singleIso F n).inv.app X ≫
        (HomotopyCategory.singleFunctor A n ⋙ Homotopy.toDerived F).map f := sorry

end singleIso


end CategoryTheory.Functor.Homotopy
