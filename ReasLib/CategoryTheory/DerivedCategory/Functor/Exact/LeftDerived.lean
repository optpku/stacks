/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors as left-derived models

An exact functor acts directly on derived categories.  This file compares that canonical action
with an arbitrary left-derived model at the homotopy-category localization.  The comparison map
is concrete data; its invertibility remains a separate proposition, so unfinished proofs cannot
select inverse morphism data.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB

namespace CategoryTheory.ExactFunctor.LeftDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The canonical map from the derived-category action of an exact functor to any specified
left-derived model of its homotopy-to-derived functor. -/
@[stacks 015F "exact functor left-derived comparison"]
noncomputable def comparison
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ))) :
    F.mapDerivedCategory ⟶ LF :=
  @Functor.leftDerivedLift
    (HomotopyCategory A (up ℤ)) (DerivedCategory A) (DerivedCategory B)
    _ _ _ LF (Functor.Homotopy.toDerived F.obj)
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    ε (HomotopyCategory.quasiIso A (up ℤ)) inferInstance hLF
    F.mapDerivedCategory F.obj.mapDerivedCategoryFactorsh.hom

/-- The exact-model comparison is characterized by the left-derived counit equation. -/
@[stacks 015F "exact functor left-derived comparison counit"]
theorem comparison_counit
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ))) :
    Functor.whiskerLeft
        (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
        (comparison F LF ε hLF) ≫ ε =
      F.obj.mapDerivedCategoryFactorsh.hom := sorry

/-- Componentwise form of the counit equation for the exact-model comparison. -/
@[stacks 015F "exact functor left-derived comparison counit component"]
theorem comparison_counit_app
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ)))
    (K : HomotopyCategory A (up ℤ)) :
    (comparison F LF ε hLF).app
        ((DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A).obj K) ≫
      ε.app K = F.obj.mapDerivedCategoryFactorsh.hom.app K := sorry

/-- The canonical comparison from an exact model to a left-derived model is invertible.  This
fact is deliberately not an instance: inverse data are formed only from an explicit proof. -/
@[stacks 015F "exact functor left-derived comparison is invertible"]
theorem comparison_isIso
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ))) :
    IsIso (comparison F LF ε hLF) := sorry

/-- Upgrade the exact-model comparison to an isomorphism from an explicit invertibility
certificate. -/
@[stacks 015F "exact functor left-derived comparison isomorphism"]
noncomputable def comparisonIso
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ)))
    (h : IsIso (comparison F LF ε hLF)) : F.mapDerivedCategory ≅ LF :=
  @asIso _ _ _ _ (comparison F LF ε hLF) h

/-- The forward map of `comparisonIso` is the canonical exact-model comparison. -/
@[simp, stacks 015F "exact functor left-derived comparison isomorphism forward map"]
theorem comparisonIso_hom
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ)))
    (h : IsIso (comparison F LF ε hLF)) :
    (comparisonIso F LF ε hLF h).hom = comparison F LF ε hLF := sorry

/-- The comparison isomorphism is independent of the proof of invertibility supplied to it. -/
@[stacks 015F "exact functor left-derived comparison proof independence"]
theorem comparisonIso_eq
    (F : A ⥤ₑ B) (LF : DerivedCategory A ⥤ DerivedCategory B)
    (ε : (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ LF ⟶
      Functor.Homotopy.toDerived F.obj)
    (hLF : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (up ℤ)))
    (h₁ h₂ : IsIso (comparison F LF ε hLF)) :
    comparisonIso F LF ε hLF h₁ = comparisonIso F LF ε hLF h₂ := sorry

end CategoryTheory.ExactFunctor.LeftDerived
