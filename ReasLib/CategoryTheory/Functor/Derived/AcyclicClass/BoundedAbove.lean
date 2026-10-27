/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.BoundedAboveReplacement
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.Algebra.Homology.HomotopyCategory.Termwise.BoundedAbove
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Above.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Left
public import ReasLib.CategoryTheory.ObjectProperty.Cover

@[expose] public section

/-!
# Bounded-Above Acyclic Classes

This leaf packages the condition that an additive functor preserves acyclicity on bounded-above
complexes with terms in a chosen object property. It separates local computation from
globalization by termwise replacements and retains source-level essential constancy throughout.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive]

/-- Stacks 0794: `P` is a bounded-above acyclic class for `F` when `F`
sends every bounded-above acyclic cochain complex with terms in `P` to an
acyclic complex. -/
@[stacks 0794]
class IsBoundedAboveAcyclicClass (P : ObjectProperty A) : Prop where
  /-- Mapping a bounded-above acyclic termwise-P complex preserves acyclicity. -/
  mapAcyclic (K : CochainComplex A ℤ) :
    CochainComplex.minus A K → K.Acyclic → CochainComplex.termsIn P K →
      ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic

namespace IsBoundedAboveAcyclicClass

variable {F : A ⥤ B} [F.Additive] {P : ObjectProperty A}

section Bounded

variable [HasDerivedCategory.{w} B]

/-- A bounded-above quasi-isomorphism between termwise-P homotopy objects is inverted after
applying F and passing to the bounded-above derived category when `P` is closed under finite
coproducts, so that the cone is again termwise-P. -/
@[stacks 0794 "denominator inversion on a bounded-above acyclic class"]
theorem map_isIso_of_quasiIso
    [F.IsBoundedAboveAcyclicClass P] [P.IsClosedUnderFiniteCoproducts]
    {K L : HomotopyCategory.Minus A} (s : K ⟶ L)
    (hK : HomotopyCategory.Minus.termsIn A P K)
    (hL : HomotopyCategory.Minus.termsIn A P L)
    (hs : HomotopyCategory.Minus.quasiIso A s) :
    IsIso (F.toBoundedAboveDerived.map s) := sorry

/-- Stacks 0794: a bounded-above homotopy object whose terms belong to a bounded-above acyclic
class computes the bounded-above left derived functor when the class contains zero, is closed
under finite coproducts, and admits epi covers. -/
@[stacks 0794]
theorem computesAt
    [F.IsBoundedAboveAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
    (K : HomotopyCategory.Minus A)
    [Functor.LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K]
    (hK : HomotopyCategory.Minus.termsIn A P K) :
    LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K := sorry

/-- A bounded-above complex with terms in an acyclic class computes the unbounded left derived
functor when the class contains zero, is closed under finite coproducts, and admits epi covers,
both categories have exact sequential colimits, and the functor preserves them. -/
@[stacks 0794]
theorem computesAt_unbounded
    [F.IsBoundedAboveAcyclicClass P]
    [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F] (K : HomotopyCategory.Minus A)
    [Functor.LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    (hK : HomotopyCategory.Minus.termsIn A P K) :
    LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj := sorry

section Existence

/-- Bounded-above termwise-P replacements make the left-derived functor source-defined
everywhere when the acyclic class contains zero, is closed under finite coproducts, and admits
epi covers. -/
@[stacks 0794 "bounded-above source-definedness"]
theorem everywhereDefined (P : ObjectProperty A)
    [F.IsBoundedAboveAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover] :
    Functor.LeftDerived.EverywhereDefined F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Stacks 0794: a bounded-above acyclic class with enough termwise
replacements defines the pointwise bounded-above left derived functor
everywhere. -/
@[stacks 0794]
theorem hasPointwise (P : ObjectProperty A)
    [F.IsBoundedAboveAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover] :
    F.toBoundedAboveDerived.HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := sorry

/-- Stacks 0794: a bounded-above acyclic class with enough termwise
replacements defines the total bounded-above left derived functor. -/
@[stacks 0794]
theorem hasFunctor (P : ObjectProperty A)
    [F.IsBoundedAboveAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteCoproducts] [P.HasEpiCover] :
    F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := sorry

end Existence

end Bounded

end IsBoundedAboveAcyclicClass



end CategoryTheory.Functor
