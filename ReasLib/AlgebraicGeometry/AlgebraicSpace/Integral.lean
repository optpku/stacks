/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Irreducible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum

/-!
# Integral algebraic spaces

An algebraic space is integral when it is reduced, decent, and its space of
points is irreducible. Decency is required: reduced and irreducible is not
étale-local on algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is integral if it is reduced, decent, and `|X|` is
irreducible. -/
@[mk_iff]
class IsIntegral {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop extends
    IsReduced X, IsDecent X, IsIrreducible X

namespace IsIntegral

/-- An integral algebraic space is reduced, decent, and irreducible. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsIntegral X] :
    IsReduced X ∧ IsDecent X ∧ IsIrreducible X :=
  sorry

/-- Reducedness, decency, and irreducibility together witness that an algebraic
space is integral. -/
@[instance 900]
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsReduced X] [IsDecent X] [IsIrreducible X] : IsIntegral X :=
  sorry

end IsIntegral

/-- A decent algebraic space is integral if and only if it is reduced and irreducible. -/
theorem isIntegral_iff_isReduced_and_isIrreducible {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] :
    IsIntegral X ↔ IsReduced X ∧ IsIrreducible X :=
  sorry

/-- An integral scheme over `S`, viewed as an algebraic space, is integral. -/
instance instIsIntegral_ofOver {S : Scheme.{u}} (T : Over S)
    [AlgebraicGeometry.IsIntegral T.left] : IsIntegral (ofOver T) where
  toIsReduced := instIsReduced_ofOver T
  toIsDecent := instIsDecent_ofOver T
  toIsIrreducible := instIsIrreducible_ofOver T

/-- The spectrum of a domain, viewed as an algebraic space over itself, is integral. -/
instance instIsIntegral_specSpace (A : Type u) [CommRing A] [IsDomain A] :
    IsIntegral (specSpace A) := by
  refine @instIsIntegral_ofOver _ (Over.mk (𝟙 (Spec (CommRingCat.of A)))) ?_
  change AlgebraicGeometry.IsIntegral (Spec (CommRingCat.of A))
  infer_instance

end AlgebraicGeometry.AlgebraicSpace
