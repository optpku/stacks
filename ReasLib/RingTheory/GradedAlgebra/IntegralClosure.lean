/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Subsemiring
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Homogeneity of integral closures

@stack 077G

This leaf records that integral closure respects compatible gradings on the
source and target rings.
-/

universe u v

namespace integralClosure

/-- Lemma 10.56.3 (077G): the integral closure along a homomorphism of
graded rings is a homogeneous subsemiring of the target. -/
@[stacks 077G]
theorem isHomogeneous
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {Agrade : ℕ → AddSubgroup R} [GradedRing Agrade]
    {Bgrade : ℕ → AddSubgroup S} [GradedRing Bgrade]
    [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ Agrade i → algebraMap R S r ∈ Bgrade i) :
    DirectSum.SetLike.IsHomogeneous Bgrade
      (integralClosure R S).toSubsemiring := sorry

/-- The underlying submodule of a homogeneous integral closure is
homogeneous for the target grading. -/
@[stacks 077G "submodule view"]
theorem toSubmodule_isHomogeneous
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    {Agrade : ℕ → AddSubgroup R} [GradedRing Agrade]
    {Bgrade : ℕ → AddSubgroup S} [GradedRing Bgrade]
    [Algebra R S]
    (hgraded : ∀ i {r : R}, r ∈ Agrade i → algebraMap R S r ∈ Bgrade i) :
    (integralClosure R S).toSubmodule.IsHomogeneous Bgrade := sorry

end integralClosure
