/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Shift.Left

@[expose] public section

/-!
# Shift Transport for Pointwise Derived Values

Convenience import for the left and right pointwise-derived shift API.  The two directional
leaves remain separate so consumers that only use one Kan-extension variance can keep imports
narrow.
-/
