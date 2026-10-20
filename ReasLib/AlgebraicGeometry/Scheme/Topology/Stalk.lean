/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.JacobsonSpace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointwise topology of spectra of local rings

This file exposes pointwise readouts of Mathlib's canonical map from the spectrum of a scheme
stalk.  The underlying set equality remains owned by `Scheme.range_fromSpecStalk`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A point lies in the image of `Spec 𝒪_{X,x} ⟶ X` exactly when it is a generalization of
`x`. -/
@[simp, stacks 01J7 "points in the image of the spectrum of a stalk"]
theorem mem_range_fromSpecStalk_iff {X : Scheme.{u}} {x y : X} :
    y ∈ Set.range (X.fromSpecStalk x) ↔ y ⤳ x := sorry

/-- For a family of closed points with open complement `U`, the inverse image of `U`
in the spectrum of each stalk is the complement of its closed point. -/
theorem preimage_fromSpecStalk_eq_puncturedOpen_of_compl_range {ι : Type}
    {S : Scheme.{u}} (U : S.Opens) (s : ι → S)
    (hs_closed : ∀ i, s i ∈ closedPoints S)
    (hU : (U : Set S) = (Set.range s)ᶜ) (i : ι) :
    ((S.fromSpecStalk (s i)) ⁻¹ᵁ U : Set (Spec (S.presheaf.stalk (s i)))) =
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}ᶜ :=
  sorry

end AlgebraicGeometry.Scheme
