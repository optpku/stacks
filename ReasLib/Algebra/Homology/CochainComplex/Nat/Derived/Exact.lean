/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.Algebra.Homology.CochainComplex.Nat.Derived
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.CategoryTheory.DerivedCategory.BoundedLocalization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors on derived nonnegative complexes

This file compares the bounded-below and unbounded realizations of a nonnegative cochain complex,
then proves that the resulting derived realization commutes canonically with an exact functor.
It is the change-of-coefficients interface needed whenever a naturally nonnegative complex is
first localized in `D⁺` and later viewed in an unbounded derived category.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CochainComplex.Nat

variable (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Extending a nonnegative complex into bounded-below complexes and localizing in `D⁺`, then
including into `D`, canonically agrees with direct extension and unbounded localization. -/
@[stacks 01EQ "bounded-below realization of a nonnegative complex"]
noncomputable def boundedToDerivedIso :
    CochainComplex.Plus.extendNat A ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
      toDerived A :=
  Functor.isoWhiskerLeft (CochainComplex.Plus.extendNat A)
      (DerivedCategory.Plus.Qh.compInclusionIso A) ≪≫
    (Functor.associator
      (CochainComplex.Plus.extendNat A) (CochainComplex.Plus.ι A)
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)).symm ≪≫
    Functor.isoWhiskerRight (CochainComplex.Plus.extendNatCompInclusionIso A)
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)

end CochainComplex.Nat

namespace CategoryTheory.ExactFunctor.MapDerivedCategory

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B]
variable [Abelian A] [Abelian B]
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Direct derived realization of a nonnegative complex commutes canonically with an exact
functor. -/
@[stacks 01EQ "exact change of coefficients for nonnegative derived complexes"]
noncomputable def nonnegativeIso (F : A ⥤ₑ B) :
    CochainComplex.Nat.toDerived A ⋙ F.mapDerivedCategory ≅
      F.obj.mapHomologicalComplex (up ℕ) ⋙ CochainComplex.Nat.toDerived B :=
  Functor.associator
      (embeddingUpNat.extendFunctor A)
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
      F.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (embeddingUpNat.extendFunctor A)
      F.obj.mapDerivedCategoryFactors ≪≫
    (Functor.associator
      (embeddingUpNat.extendFunctor A)
      (F.obj.mapHomologicalComplex (up ℤ))
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)).symm ≪≫
    Functor.isoWhiskerRight
      (ComplexShape.Embedding.mapFunctorIso embeddingUpNat F.obj)
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) ≪≫
    Functor.associator
      (F.obj.mapHomologicalComplex (up ℕ))
      (embeddingUpNat.extendFunctor B)
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)

end CategoryTheory.ExactFunctor.MapDerivedCategory

namespace CategoryTheory.ExactFunctor.Derived.Nat

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Category.{vB} B]
variable [Abelian A] [Abelian B]
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- Localizing a nonnegative `A`-complex in `D⁺(A)`, including it in `D(A)`, and applying an
exact functor agrees canonically with applying the functor termwise before the corresponding
bounded-below realization in `B`. -/
@[stacks 01EQ "bounded-below exact change of coefficients for nonnegative complexes"]
noncomputable def iso (F : A ⥤ₑ B) :
    (CochainComplex.Plus.extendNat A ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) ⋙
      F.mapDerivedCategory ≅
      F.obj.mapHomologicalComplex (up ℕ) ⋙
        CochainComplex.Plus.extendNat B ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι :=
  Functor.isoWhiskerRight (CochainComplex.Nat.boundedToDerivedIso A)
      F.mapDerivedCategory ≪≫
    MapDerivedCategory.nonnegativeIso F ≪≫
    Functor.isoWhiskerLeft (F.obj.mapHomologicalComplex (up ℕ))
      (CochainComplex.Nat.boundedToDerivedIso B).symm

end CategoryTheory.ExactFunctor.Derived.Nat
