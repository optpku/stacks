/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.ObjectProperty
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Unbounded Left Derived Functors from Acyclic Objects

This file gives the bounded-above dual of the unbounded right-derived acyclic criterion. The
public statements use epimorphic covers by bounded left-acyclic objects and the canonical
bounded-above left-derived degrees, without chosen projective resolutions or opposite transport.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftAcyclic.Unbounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
  [(LeftAcyclic.Bounded F).HasEpiCover]

/-- Stacks 07K8 (1): enough bounded left-acyclic objects and vanishing of one bounded-derived
degree make the unbounded left derived functor source-defined everywhere. -/
@[stacks 07K8]
theorem everywhereDefined_of_vanishes
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n) :
    LeftDerived.EverywhereDefined (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

namespace Termwise

/-- Stacks 07K8 (2): a complex of bounded left-acyclic objects computes the unbounded left
derived value under the finite-dimensionality hypothesis. -/
@[stacks 07K8]
theorem computesAt
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    (K : CochainComplex.TermsIn ℤ (LeftAcyclic.Bounded F)) :
    LeftDerived.ComputesAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ))
      ((HomotopyCategory.quotient A (up ℤ)).obj K.obj) := sorry

/-- Stacks 07K8 (3): every cochain complex receives a quasi-isomorphism from a complex of
bounded left-acyclic objects under the finite-dimensionality hypothesis. -/
@[stacks 07K8]
theorem existsQuasiIsoFrom
    (n : ℕ) (h_n : LeftDerived.Bounded.Vanishes.inDegree F n)
    (K : CochainComplex A ℤ) :
    ∃ (L : CochainComplex.TermsIn ℤ (LeftAcyclic.Bounded F))
      (α : L.obj ⟶ K), QuasiIso α := sorry

end Termwise

end CategoryTheory.Functor.LeftAcyclic.Unbounded
