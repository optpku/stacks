/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors detected on short exact sequences

The criteria below deliberately phrase mapped exactness through a composable
pair of morphisms. This avoids requiring a `PreservesZeroMorphisms` instance
before the criterion itself has established the relevant exactness property.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B)

/-- A functor between abelian categories is left exact precisely when it maps each short exact
complex to an exact composable pair whose first map is monic. -/
@[stacks 010N]
theorem leftExact_iff_maps_shortExact :
    leftExactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Mono (F.map S.f) := sorry

/-- A functor between abelian categories is right exact precisely when it maps each short exact
complex to an exact composable pair whose second map is epic. -/
@[stacks 010N]
theorem rightExact_iff_maps_shortExact :
    rightExactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Epi (F.map S.g) := sorry

/-- A functor between abelian categories is exact precisely when it maps each short exact complex
to an exact composable pair with monic first and epic second map. -/
@[stacks 010N]
theorem exact_iff_maps_shortExact :
    exactFunctor A B F ↔
      ∀ (S : ShortComplex A),
        S.ShortExact → (ComposableArrows.mk₂ (F.map S.f) (F.map S.g)).Exact ∧
          Mono (F.map S.f) ∧ Epi (F.map S.g) := sorry

/-- A finite-limit-preserving additive functor maps a short exact complex to an exact short
complex. -/
@[stacks 015D "finite-limit exactness on short exact complexes"]
theorem exact_of_preservesFiniteLimits [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map F).Exact := sorry

/-- A finite-limit-preserving additive functor maps the first morphism of a short exact complex
to a monomorphism. -/
@[stacks 015D "finite-limit preservation of the first monomorphism"]
theorem mono_of_preservesFiniteLimits [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    Mono (F.map S.f) := sorry

/-- A finite-limit-preserving additive functor maps a short exact complex to a short exact
complex when the mapped second morphism is epic. -/
@[stacks 015D "finite-limit short exactness criterion"]
theorem shortExact_of_preservesFiniteLimits
    [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) [Epi (F.map S.g)] :
    (S.map F).ShortExact := sorry

/-- Explicit-premise form of `shortExact_of_preservesFiniteLimits`. -/
@[stacks 015D "explicit finite-limit short exactness criterion"]
theorem shortExact_of_preservesFiniteLimits_of
    [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := sorry

/-- A finite-colimit-preserving additive functor maps a short exact complex to an exact short
complex. -/
@[stacks 015D "finite-colimit exactness on short exact complexes"]
theorem exact_of_preservesFiniteColimits [F.Additive] [PreservesFiniteColimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map F).Exact := sorry

/-- A finite-colimit-preserving additive functor maps the second morphism of a short exact complex
to an epimorphism. -/
@[stacks 015D "finite-colimit preservation of the second epimorphism"]
theorem epi_of_preservesFiniteColimits [F.Additive] [PreservesFiniteColimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    Epi (F.map S.g) := sorry

/-- A finite-colimit-preserving additive functor maps a short exact complex to a short exact
complex when the mapped first morphism is monic. -/
@[stacks 015D "finite-colimit short exactness criterion"]
theorem shortExact_of_preservesFiniteColimits
    [F.Additive] [PreservesFiniteColimits F]
    {S : ShortComplex A} (hS : S.ShortExact) [Mono (F.map S.f)] :
    (S.map F).ShortExact := sorry

/-- Explicit-premise form of `shortExact_of_preservesFiniteColimits`. -/
@[stacks 015D "explicit finite-colimit short exactness criterion"]
theorem shortExact_of_preservesFiniteColimits_of
    [F.Additive] [PreservesFiniteColimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (h_mono : Mono (F.map S.f)) :
    (S.map F).ShortExact := sorry

/-- Stacks 015D source-facing form of `exact_of_preservesFiniteLimits`. -/
@[stacks 015D]
theorem exact_map_of_shortExact [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    (S.map F).Exact := sorry

/-- Stacks 015D source-facing form of `mono_of_preservesFiniteLimits`. -/
@[stacks 015D]
theorem mono_map_f_of_shortExact [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) :
    Mono (F.map S.f) := sorry

/-- Stacks 015D source-facing explicit-premise form of
`shortExact_of_preservesFiniteLimits`. -/
@[stacks 015D]
theorem map_shortExact_of_epi_map_g
    [F.Additive] [PreservesFiniteLimits F]
    {S : ShortComplex A} (hS : S.ShortExact) (h_epi : Epi (F.map S.g)) :
    (S.map F).ShortExact := sorry

end CategoryTheory.Functor
