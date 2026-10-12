/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

@[expose] public section

noncomputable section

universe u

namespace localCohomology

/-- Every local cohomology module of a finite module over a Noetherian local ring,
supported at the maximal ideal, is Artinian. -/
instance instIsArtinianMaximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : ModuleCat.{u} A) [Module.Finite A M] (i : ℕ) :
    IsArtinian A ((localCohomology (IsLocalRing.maximalIdeal A) i).obj M) := sorry

end localCohomology
