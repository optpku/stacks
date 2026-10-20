/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Ring.Aut
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Automorphisms of roots of unity

An automorphism of a commutative monoid preserves every group of roots of unity.  This file
packages that restriction functorially as a homomorphism of automorphism groups.
@stack 0BU5
-/

universe u

namespace MulAut

variable {R : Type u} [CommMonoid R]

/-- Restriction to `n`th roots of unity sends the identity automorphism to the identity. -/
theorem restrictRootsOfUnity_one (n : ℕ) :
    (1 : MulAut R).restrictRootsOfUnity n = 1 := sorry

/-- Restriction to `n`th roots of unity preserves composition of automorphisms. -/
theorem restrictRootsOfUnity_mul (n : ℕ) (sigma tau : MulAut R) :
    (sigma * tau).restrictRootsOfUnity n =
      sigma.restrictRootsOfUnity n * tau.restrictRootsOfUnity n := sorry

/-- Restrict automorphisms of a commutative monoid to its group of `n`th roots of unity. -/
@[stacks 0BU5 "automorphism action on roots of unity"]
def restrictRootsOfUnityHom (n : ℕ) :
    MulAut R →* MulAut (rootsOfUnity n R) where
  toFun sigma := sigma.restrictRootsOfUnity n
  map_one' := restrictRootsOfUnity_one n
  map_mul' := restrictRootsOfUnity_mul n

/-- The roots-of-unity automorphism homomorphism acts by the usual restriction. -/
@[simp, stacks 0BU5 "automorphism action on roots of unity formula"]
theorem restrictRootsOfUnityHom_apply (n : ℕ) (sigma : MulAut R) :
    restrictRootsOfUnityHom n sigma = sigma.restrictRootsOfUnity n := sorry

end MulAut
