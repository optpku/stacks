/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality formulas for truncation-filtration realization maps

These equations expose and invert the page-two and abutment comparison squares.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB uC vC

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- The page-two naturality law exposed as a theorem. -/
@[reassoc, stacks 0BKM "page-two naturality for a truncation-filtration realization map"]
theorem Map.pageTwo_naturality {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (i : ℕ) (j : ℤ) :
    (m.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j) ≫ (T.pageTwoIso i j).hom =
      (S.pageTwoIso i j).hom ≫
        (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f) := sorry

/-- The abutment naturality law exposed as a theorem. -/
@[reassoc, stacks 0BKM "abutment naturality for a truncation-filtration realization map"]
theorem Map.target_naturality {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f := sorry

/-- Naturality of the inverse page-two comparison for a truncation-filtration realization map. -/
@[reassoc, stacks 0BKM
  "inverse-comparison naturality for a truncation-filtration realization map"]
theorem Map.pageTwo_inv_naturality {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (i : ℕ) (j : ℤ) :
    (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f) ≫
        (T.pageTwoIso i j).inv =
      (S.pageTwoIso i j).inv ≫
        (m.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j) := sorry

/-- Naturality of the inverse abutment comparison for a truncation-filtration realization map. -/
@[reassoc, stacks 0BKM
  "inverse abutment-comparison naturality for a truncation-filtration realization map"]
theorem Map.target_inv_naturality {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (n : ℤ) :
    (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f ≫
        (T.targetIso n).inv =
      (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- The page-two comparison can be inverted to recover the underlying renumbered
spectral-sequence map. -/
@[reassoc, stacks 0BKM "inverse page-two naturality for a truncation-filtration realization map"]
theorem Map.pageTwo_naturality_inv {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (i : ℕ) (j : ℤ) :
    (S.pageTwoIso i j).hom ≫
        (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f) ≫
        (T.pageTwoIso i j).inv =
      (m.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j) := sorry

/-- Conjugating the truncation-filtration model page map by the inverse comparisons recovers the
second-page right-derived map. -/
@[reassoc, stacks 0BKM "target-map computation for a truncation-filtration second page"]
theorem Map.pageTwo_target_map {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (i : ℕ) (j : ℤ) :
    (S.pageTwoIso i j).inv ≫
        (m.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j) ≫
      (T.pageTwoIso i j).hom =
      (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f) := sorry

/-- The abutment comparison can be inverted to recover the underlying homology map. -/
@[reassoc, stacks 0BKM "inverse abutment naturality for a truncation-filtration realization map"]
theorem Map.target_naturality_inv {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).hom ≫
        (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f ≫
        (T.targetIso n).inv =
      HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the truncation-filtration model abutment map by the inverse comparisons recovers
the derived cohomology map. -/
@[reassoc, stacks 0BKM "target-map computation for a truncation-filtration abutment"]
theorem Map.target_map {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n ≫
      (T.targetIso n).hom =
      (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
