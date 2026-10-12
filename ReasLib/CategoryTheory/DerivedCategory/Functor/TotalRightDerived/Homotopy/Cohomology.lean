/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy

/-!
# Cohomology of unbounded total right-derived functors

This leaf exposes the cochain-level value and cohomology functors attached to the
construction-neutral total right-derived functor.  Filtered, geometric, and spectral-sequence
applications can therefore use the ordinary functorial API instead of rebuilding object and map
formulas.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.Functor.RightDerived.Homotopy

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The cochain-level total right-derived functor of an additive functor. -/
@[stacks 05S9 "cochain-level total right-derived functor"]
abbrev cochainFunctor (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    CochainComplex A ℤ ⥤ DerivedCategory B :=
  (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ functor F

/-- Degree-`n` cohomology after applying an unbounded total right-derived functor. -/
@[stacks 05S9 "cohomology after an unbounded total right-derived functor"]
abbrev cohomologyFunctor (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] (n : ℤ) :
    DerivedCategory A ⥤ B :=
  functor F ⋙ DerivedCategory.homologyFunctor B n

/-- Degree-`n` cohomology after localizing a cochain complex and applying an unbounded total
right-derived functor. -/
@[stacks 05S9 "cochain-level unbounded total right-derived cohomology"]
abbrev cochainCohomologyFunctor (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] (n : ℤ) :
    CochainComplex A ℤ ⥤ B :=
  cochainFunctor F ⋙ DerivedCategory.homologyFunctor B n

/-- The degree-`n` cohomology of the unbounded total right-derived value of a cochain complex. -/
@[stacks 05S9 "unbounded total right-derived cohomology"]
abbrev cochainCohomology (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (K : CochainComplex A ℤ) (n : ℤ) : B :=
  (cochainCohomologyFunctor F n).obj K

/-- The map on unbounded total right-derived cohomology induced by a cochain map. -/
@[stacks 05S9 "map on unbounded total right-derived cohomology"]
abbrev cochainCohomologyMap (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    cochainCohomology F K n ⟶ cochainCohomology F L n :=
  (cochainCohomologyFunctor F n).map f



end CategoryTheory.Functor.RightDerived.Homotopy
