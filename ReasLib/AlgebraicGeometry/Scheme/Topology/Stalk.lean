/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
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

end AlgebraicGeometry.Scheme
