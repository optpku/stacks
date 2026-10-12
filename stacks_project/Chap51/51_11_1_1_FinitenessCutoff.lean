/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalCohomology.Cutoff
public import ReasLib.RingTheory.Depth.Localization
public import ReasLib.RingTheory.Ideal.Localization

universe u v

/- The cutoff API is owned by `ReasLib.RingTheory.LocalCohomology.Cutoff`. -/
#check (Module.LocalCohomology.cutoff :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A],
    (I : Ideal A) → (M : Type v) → [AddCommGroup M] → [Module A M] →
      [Module.Finite A M] → WithBot ℕ∞)
