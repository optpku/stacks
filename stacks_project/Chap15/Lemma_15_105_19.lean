/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Localization.Pi
public import ReasLib.RingTheory.WeakDimension.Pi

/-!
# Lemma 15.105.19

@stack 092T
-/

@[expose] public section

universe u v w

/- Lemma 15.105.19 (1): an arbitrary product of valuation rings has weak dimension at most one.
This is the valuation specialization of the reusable Bezout-domain product instance. -/
@[stacks 092T "Lemma 15.105.19 (1)"]
#check fun {J : Type u} (A : J → Type v)
    [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)] ↦
  (inferInstance : HasWeakDimensionLE ((j : J) → A j) 1)

/- Lemma 15.105.19 (2): products of fraction rings are the localization of the product at the
submonoid of componentwise nonzerodivisors. -/
@[stacks 092T "Lemma 15.105.19 (2)"]
#check fun {J : Type u} (A : J → Type v) (K : J → Type w)
    [∀ j, CommRing (A j)] [∀ j, CommRing (K j)]
    [∀ j, IsDomain (A j)] [∀ j, ValuationRing (A j)]
    [∀ j, Algebra (A j) (K j)] [∀ j, IsFractionRing (A j) (K j)] ↦
  (inferInstance :
    IsLocalization (Submonoid.pi Set.univ fun j ↦ nonZeroDivisors (A j))
      ((j : J) → K j))
