/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import ReasLib.Algebra.Homology.CochainComplex.BoundedBelowReplacement
public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.Algebra.Homology.HomotopyCategory.QuasiIso.Bounded
public import ReasLib.Algebra.Homology.HomotopyCategory.Termwise.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Basic
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Subset.Right
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Acyclic Classes

This leaf packages the property that an additive functor preserves acyclicity on bounded-below
complexes whose terms lie in a chosen object property. It separates the local computation
criterion from globalization by termwise replacements, and retains source-level essential
constancy throughout.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B]
  (F : A ⥤ B) [F.Additive]

/-- A bounded-below acyclic class for F is an object property such that F sends every
bounded-below acyclic complex with terms in that property to an acyclic complex. -/
@[stacks 05TA "bounded-below acyclic class"]
class IsBoundedBelowAcyclicClass (P : ObjectProperty A) : Prop where
  /-- Mapping a bounded-below acyclic termwise-P complex preserves acyclicity. -/
  mapAcyclic (K : CochainComplex A ℤ) :
    CochainComplex.plus A K → K.Acyclic → CochainComplex.termsIn P K →
      ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic

namespace IsBoundedBelowAcyclicClass

variable {F : A ⥤ B} [F.Additive] {P : ObjectProperty A}

/-- A bounded-below quasi-isomorphism between termwise-P homotopy objects is inverted after
applying F and passing to the bounded-below derived category when `P` is closed under finite
products, so that the cone is again termwise-P. -/
@[stacks 05TA "denominator inversion on a bounded-below acyclic class"]
theorem map_isIso_of_quasiIso
    [HasDerivedCategory.{w} B] [F.IsBoundedBelowAcyclicClass P]
    [P.IsClosedUnderFiniteProducts]
    {K L : HomotopyCategory.Plus A} (s : K ⟶ L)
    (hK : HomotopyCategory.Plus.termsIn A P K)
    (hL : HomotopyCategory.Plus.termsIn A P L)
    (hs : HomotopyCategory.Plus.quasiIso A s) :
    IsIso (F.toBoundedBelowDerived.map s) := sorry

/-- A termwise-P bounded-below homotopy object computes its source-defined right-derived value
when the acyclic class contains zero, is closed under finite products, and admits mono
embeddings. -/
@[stacks 05TA "local computation from a bounded-below acyclic class"]
theorem computesAt
    [HasDerivedCategory.{w} B] [F.IsBoundedBelowAcyclicClass P]
    [P.ContainsZero] [P.IsClosedUnderFiniteProducts] [P.HasMonoEmbedding]
    (K : HomotopyCategory.Plus A)
    [Functor.RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K]
    (hK : HomotopyCategory.Plus.termsIn A P K) :
    RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

section Global

variable [HasDerivedCategory.{w} B]

/-- Termwise-P bounded-below replacements make the right-derived functor source-defined
everywhere when the acyclic class contains zero, is closed under finite products, and admits
mono embeddings. -/
@[stacks 05TA "globalization from a bounded-below acyclic class"]
theorem everywhereDefined (P : ObjectProperty A)
    [F.IsBoundedBelowAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteProducts] [P.HasMonoEmbedding] :
    Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The source-defined globalization supplies Mathlib's pointwise right-derived functor. -/
theorem hasPointwise (P : ObjectProperty A)
    [F.IsBoundedBelowAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteProducts] [P.HasMonoEmbedding] :
    F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The source-defined globalization supplies the total bounded-below right-derived functor. -/
theorem hasFunctor (P : ObjectProperty A)
    [F.IsBoundedBelowAcyclicClass P] [P.ContainsZero]
    [P.IsClosedUnderFiniteProducts] [P.HasMonoEmbedding] :
    F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A) := sorry

end Global

end IsBoundedBelowAcyclicClass



end CategoryTheory.Functor
