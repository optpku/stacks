/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded Right Derived Functors from Acyclic Objects

@stack 07K7

This file gives the resolution-independent form of the finite-cohomological-dimension criterion.
The hypotheses use the canonical bounded-below right derived functor and enough bounded
right-acyclic objects; no chosen injective resolutions enter the public statements.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.RightAcyclic.Unbounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
  [(RightAcyclic.Bounded F).HasMonoEmbedding]

/-- Stacks 07K7 (1): enough bounded right-acyclic objects and vanishing of one bounded-derived
degree make the unbounded right derived functor source-defined everywhere. -/
@[stacks 07K7]
theorem everywhereDefined_of_vanishes
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n) :
    RightDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

namespace Termwise

/-- Stacks 07K7 (2): a complex of bounded right-acyclic objects computes the unbounded right
derived value under the finite-dimensionality hypothesis. -/
@[stacks 07K7]
theorem computesAt
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    (K : CochainComplex.TermsIn ℤ (RightAcyclic.Bounded F)) :
    RightDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K.obj) := sorry

/-- Stacks 07K7 (3): every cochain complex maps by a quasi-isomorphism to a complex of bounded
right-acyclic objects under the finite-dimensionality hypothesis. -/
@[stacks 07K7]
theorem existsQuasiIsoTo
    (n : ℕ) (h_n : RightDerived.Bounded.Vanishes.inDegree F n)
    (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex.TermsIn ℤ (RightAcyclic.Bounded F))
      (α : K ⟶ L.obj), QuasiIso α := sorry

end Termwise

end CategoryTheory.Functor.RightAcyclic.Unbounded
