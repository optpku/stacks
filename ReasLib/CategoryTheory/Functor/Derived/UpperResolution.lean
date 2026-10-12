/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.Truncation.UpperResolution.Colimit
public import ReasLib.CategoryTheory.Functor.Derived.AcyclicClass.BoundedAbove
public import ReasLib.CategoryTheory.Preadditive.RightExact

@[expose] public section

/-!
# Left Derived Functors from Upper-Resolution Towers

This leaf promotes the bounded computation API from
`Functor.IsBoundedAboveAcyclicClass` along compatible upper-resolution towers.
Exact sequential colimits make their colimit objects compute the unbounded
left derived functor.
-/

open CategoryTheory CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CochainComplex.UpperTruncation.Resolution

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
variable {P : ObjectProperty A} {K : CochainComplex A ℤ}
variable [HasColimitsOfShape ℕ B] [HasExactColimitsOfShape ℕ B]

/-- Stacks 0794: the colimit of an upper-resolution tower computes the
unbounded left derived functor whenever the target has exact sequential
colimits and the original functor preserves them. -/
@[stacks 0794]
theorem colimit_computesLeftDerivedAt
    (S : UpperTruncation.Resolution P K) [HasColimit S.tower] (F : A ⥤ B)
    [F.Additive] [PreservesColimitsOfShape ℕ F]
    (hF : F.IsBoundedAboveAcyclicClass P) :
    CategoryTheory.Functor.LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj (colimit S.tower)) := sorry

/-- Stacks 0794: an upper-resolution whose colimit comparison is a
quasi-isomorphism gives pointwise left-derived existence at its target. -/
@[stacks 0794]
theorem hasPointwiseLeftDerivedFunctorAt
    (S : UpperTruncation.Resolution P K) [HasColimit S.tower] (F : A ⥤ B)
    [F.Additive] [PreservesColimitsOfShape ℕ F]
    (hF : F.IsBoundedAboveAcyclicClass P) [QuasiIso S.fromColimit] :
    (Functor.Homotopy.toDerived F).HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K) := sorry

end CochainComplex.UpperTruncation.Resolution

namespace CategoryTheory.Functor.IsBoundedAboveAcyclicClass

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
variable {F : A ⥤ B} [F.Additive]
variable {P : ObjectProperty A}
  [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
variable [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
variable [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
variable [PreservesColimitsOfShape ℕ F]

/-- Stacks 0794: every cochain complex admits an upper resolution whose
colimit is quasi-isomorphic to the complex and computes the unbounded left
derived functor. This combines `exists_with_quasiIso_fromColimit` with
`Resolution.colimit_computesLeftDerivedAt`. -/
@[stacks 0794]
theorem exists_resolution_computingLeftDerivedAt
    (hF : F.IsBoundedAboveAcyclicClass P) (K : CochainComplex A ℤ) :
    ∃ S : CochainComplex.UpperTruncation.Resolution P K,
      QuasiIso S.fromColimit ∧
        CategoryTheory.Functor.LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
          (HomotopyCategory.quasiIso A (up ℤ))
          ((HomotopyCategory.quotient A (up ℤ)).obj (colimit S.tower)) := sorry

/-- Stacks 0794: exact sequential colimits and a bounded-above acyclic
class give pointwise left-derived existence at an arbitrary cochain complex. -/
@[stacks 0794]
theorem hasPointwiseLeftDerivedFunctorAt
    (hF : F.IsBoundedAboveAcyclicClass P) (K : CochainComplex A ℤ) :
    (Functor.Homotopy.toDerived F).HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K) := sorry

/-- Stacks 0794: exact sequential colimits promote a bounded-above acyclic
class to pointwise left-derived existence on the whole homotopy category. -/
@[stacks 0794]
theorem hasPointwiseLeftDerivedFunctor
    (hF : F.IsBoundedAboveAcyclicClass P) :
    (Functor.Homotopy.toDerived F).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- Stacks 0794: exact sequential colimits promote a bounded-above acyclic
class to a total left derived functor on the unbounded derived category. -/
@[stacks 0794]
theorem hasLeftDerivedFunctor
    (hF : F.IsBoundedAboveAcyclicClass P) :
    (Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

end CategoryTheory.Functor.IsBoundedAboveAcyclicClass

namespace CategoryTheory.Functor.IsBoundedAboveAcyclicClass

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]
variable {F : A ⥤ B} [PreservesFiniteColimits F]
variable {P : ObjectProperty A}
  [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
variable [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
variable [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
variable [PreservesColimitsOfShape ℕ F]

/-- Proposition 13.29.2 (Stacks 0794): a right exact functor with a
bounded-above acyclic class and the stated exact sequential-colimit
hypotheses has a total unbounded left derived functor. -/
@[stacks 0794]
theorem hasLeftDerivedFunctor_of_rightExact
    (hF : F.IsBoundedAboveAcyclicClass P) :
    (Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

end CategoryTheory.Functor.IsBoundedAboveAcyclicClass
