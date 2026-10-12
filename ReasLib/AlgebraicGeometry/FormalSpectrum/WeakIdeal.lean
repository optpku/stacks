/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Directed
public import ReasLib.RingTheory.Topology.WeaklyAdmissible

/-!
# Weak ideals of definition ordered by reverse inclusion

Weak ideals of definition index quotient spectra, with reverse inclusion giving
the direction of their transition morphisms.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- Weak ideals of definition ordered by reverse inclusion of ideals. -/
abbrev WeakIdealOfDefinition (A : Type u) [CommRing A] [TopologicalSpace A] :=
  OrderDual {I : Ideal A // TopologicalRing.Ideal.IsWeakIdealOfDefinition I}

/-- The underlying ideal of a weak ideal of definition. -/
def WeakIdealOfDefinition.ideal {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : WeakIdealOfDefinition A) : Ideal A :=
  I.val

/-- The underlying ideal of an index is a weak ideal of definition. -/
theorem WeakIdealOfDefinition.isWeak {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : WeakIdealOfDefinition A) : TopologicalRing.Ideal.IsWeakIdealOfDefinition I.ideal := sorry

/-- An ideal with its weak-ideal property defines a reverse-inclusion index. -/
def WeakIdealOfDefinition.of {A : Type u} [CommRing A] [TopologicalSpace A] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) : WeakIdealOfDefinition A :=
  ⟨I, hI⟩

/-- The weak-ideal constructor recovers its ideal and its weak-ideal property. -/
theorem WeakIdealOfDefinition.of_spec {A : Type u} [CommRing A] [TopologicalSpace A]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    (WeakIdealOfDefinition.of I hI).ideal = I ∧
      TopologicalRing.Ideal.IsWeakIdealOfDefinition (WeakIdealOfDefinition.of I hI).ideal := sorry

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- Weak ideals of definition are directed under reverse inclusion. -/
instance WeakIdealOfDefinition.instIsDirected : IsDirected (WeakIdealOfDefinition A) (· ≤ ·) :=
  sorry

/-- A weakly pre-admissible ring has a weak ideal of definition. -/
instance WeakIdealOfDefinition.instNonempty [TopologicalRing.IsWeaklyPreadmissibleRing A] :
    Nonempty (WeakIdealOfDefinition A) := sorry

/-- Comparison of weak ideals of definition is reverse inclusion of their ideals. -/
theorem WeakIdealOfDefinition.le_iff {I J : WeakIdealOfDefinition A} :
    I ≤ J ↔ J.ideal ≤ I.ideal := sorry

end AlgebraicGeometry.AffineFormalAlgebraicSpace
