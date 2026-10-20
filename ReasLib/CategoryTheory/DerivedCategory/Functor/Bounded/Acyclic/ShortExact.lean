/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.ShortExact.Left
public import ReasLib.CategoryTheory.Functor.Exactness.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Short Exact Sequences of Bounded Derived-Acyclic Objects

This umbrella exposes the left- and right-derived closure and mapped-short-exactness API.  The
declarations below own the bounded-below right-derived half; the public bounded-above left-derived
dual is provided by `ShortExact.Left`.  Both halves use the canonical acyclicity predicates and do
not depend on a chosen derived category of the source.
-/

open CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive] [PreservesFiniteLimits F]
  [F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctor
    (HomotopyCategory.Plus.quasiIso 𝒜)]

/-- Stacks 015D: bounded-below right-acyclic objects for a left exact additive functor are
closed under short exact extensions. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.isClosedUnderExtensions :
    ObjectProperty.IsClosedUnderExtensions
      (RightAcyclic.Bounded F : ObjectProperty 𝒜) := sorry

attribute [instance] RightAcyclic.Bounded.isClosedUnderExtensions

/-- Stacks 015D (1): the middle term of a short exact complex is bounded-below right acyclic
when both outer terms are. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.middle_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : RightAcyclic.Bounded F S.X₁)
    (h₃ : RightAcyclic.Bounded F S.X₃) :
    RightAcyclic.Bounded F S.X₂ := sorry

/-- Stacks 015D: the image of the right morphism of a short exact complex is epic when both
outer terms are bounded-below right acyclic. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.epi_map_g_of_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : RightAcyclic.Bounded F S.X₁)
    (h₃ : RightAcyclic.Bounded F S.X₃) :
    Epi (F.map S.g) := sorry

/-- Stacks 015D (2): a left exact additive functor maps a short exact complex to a short exact
complex when both outer terms are bounded-below right acyclic. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.map_shortExact_of_ends
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : RightAcyclic.Bounded F S.X₁)
    (h₃ : RightAcyclic.Bounded F S.X₃) :
    (S.map F).ShortExact := sorry

/-- Stacks 015D (3): the cokernel term of a short exact complex is bounded-below right acyclic
when its first two terms are. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.cokernel_of_shortExact
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : RightAcyclic.Bounded F S.X₁)
    (h₂ : RightAcyclic.Bounded F S.X₂) :
    RightAcyclic.Bounded F S.X₃ := sorry

/-- Stacks 015D (4): a left exact additive functor maps a short exact complex to a short exact
complex when its first two terms are bounded-below right acyclic. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.map_shortExact_of_left_middle
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₁ : RightAcyclic.Bounded F S.X₁)
    (h₂ : RightAcyclic.Bounded F S.X₂) :
    (S.map F).ShortExact := sorry

/-- Stacks 015D (5): the kernel term of a short exact complex is bounded-below right acyclic
when the last two terms are and the image of the right morphism is epic. -/
@[stacks 015D]
theorem RightAcyclic.Bounded.kernel_of_shortExact_of_epi_map_g
    {S : ShortComplex 𝒜} (hS : S.ShortExact)
    (h₂ : RightAcyclic.Bounded F S.X₂)
    (h₃ : RightAcyclic.Bounded F S.X₃)
    (h_epi : Epi (F.map S.g)) :
    RightAcyclic.Bounded F S.X₁ := sorry

end CategoryTheory.Functor
