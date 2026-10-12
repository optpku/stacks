/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Formally unramified maps of complete discrete valuation rings

A uniformizer and residue-field criterion for an essentially finite type map
between complete discrete valuation rings to be formally unramified.
-/

@[expose] public section

open Ideal IsLocalRing

universe u v

namespace Algebra.FormallyUnramified

/-- For an essentially finite type local map of complete discrete valuation
rings, formal unramifiedness is equivalent to a chosen source uniformizer
mapping to a target uniformizer and the residue-field extension being finite
and separable. -/
theorem iff_uniformizer_and_residueField
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
    [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]
    (π : A) (hπ : maximalIdeal A = Ideal.span ({π} : Set A)) :
    (Algebra.FormallyUnramified A B ∧ Algebra.EssFiniteType A B) ↔
      maximalIdeal B = Ideal.span ({algebraMap A B π} : Set B) ∧
      FiniteDimensional (ResidueField A) (ResidueField B) ∧
      Algebra.IsSeparable (ResidueField A) (ResidueField B) ∧
      Algebra.EssFiniteType A B := sorry

end Algebra.FormallyUnramified
