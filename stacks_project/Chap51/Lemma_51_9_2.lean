/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Depth.Openness
import StacksCheckRecall

@[expose] public section

open scoped ENat

universe u v

/- Lemma 51.9.2: If a finite module over a Noetherian ring has finite depth
`e` at a prime `p`, then some nonempty relatively open subset of `V(p)` has
depth at least `e` everywhere, with depth equal to `e` at only finitely many
points. -/
@[stacks 0DWY] #check (Module.exists_open_depth_ge_and_finite_eq :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
      (p : PrimeSpectrum A) (e : ℕ)
      (hdepth : moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) = (e : ℕ∞)),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      (U ∩ PrimeSpectrum.zeroLocus p.asIdeal).Nonempty ∧
      (∀ q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal,
        (e : ℕ∞) ≤ moduleDepth (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M)) ∧
      Set.Finite {q ∈ U ∩ PrimeSpectrum.zeroLocus p.asIdeal |
        moduleDepth (Localization.AtPrime q.asIdeal)
          (LocalizedModule.AtPrime q.asIdeal M) = (e : ℕ∞)})
