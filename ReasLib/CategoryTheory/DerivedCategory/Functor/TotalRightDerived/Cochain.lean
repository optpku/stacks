/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.Cochain

@[expose] public section

/-!
# Total Right Derived Functors of Cochain-Level Additive Functors

For an additive functor `F : A ⥤ B` between abelian categories, this module isolates the
cochain-level functor `F.mapHomologicalComplex (up ℤ) ⋙ DerivedCategory.Q`.  When that
functor admits a total right derived functor with respect to quasi-isomorphisms, the resulting
functor `DerivedCategory A ⥤ DerivedCategory B`, its comparison unit, and its universal
right-derived-functor witness are available here.

Unlike the K-injective construction in `TotalRightDerived.lean`, this API assumes only the
chosen `HasRightDerivedFunctor` instance.  It therefore applies to differential graded modules
and to any other abelian category where right derivability has been established separately.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB

namespace CategoryTheory.Functor

section

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Preadditive A]
variable [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The cochain-level functor induced by an additive functor, followed by localization in the
target derived category. -/
@[stacks 05TH "cochain-level functor followed by derived localization"]
abbrev RightDerived.Cochain.toDerived (F : A ⥤ B) [F.Additive] :
    CochainComplex A ℤ ⥤ DerivedCategory B :=
  Derived.Cochain.toDerived F


end


section

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The total right derived functor of the cochain-level functor induced by `F`. -/
@[stacks 05TH "total right derived functor of a cochain-level functor"]
abbrev RightDerived.Cochain.functor
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (RightDerived.Cochain.toDerived F).totalRightDerived
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))

/-- The canonical comparison unit from the cochain-level functor of `F` to its total right
derived functor. -/
@[stacks 05TH "cochain-level total right derived comparison unit"]
abbrev RightDerived.Cochain.unit
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (up ℤ))] :
    RightDerived.Cochain.toDerived F ⟶
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙
        RightDerived.Cochain.functor F :=
  (RightDerived.Cochain.toDerived F).totalRightDerivedUnit
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
    (HomologicalComplex.quasiIso A (up ℤ))

/-- The total right derived functor of the cochain-level functor induced by `F` satisfies the
canonical right-derived universal property with respect to quasi-isomorphisms. -/
@[stacks 05TH "cochain-level total right derived universal property"]
noncomputable instance RightDerived.Cochain.isRightDerived
    (F : A ⥤ B) [F.Additive]
    [Functor.HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived F)
      (HomologicalComplex.quasiIso A (up ℤ))] :
    (RightDerived.Cochain.functor F).IsRightDerivedFunctor
      (RightDerived.Cochain.unit F)
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry


end

end CategoryTheory.Functor
