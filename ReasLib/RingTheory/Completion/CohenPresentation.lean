/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.CoefficientRing
public import ReasLib.RingTheory.Completion.CohenRing

/-!
# Cohen power-series presentations

A complete local ring with finitely generated maximal ideal is a quotient of a finite-variable
power-series ring over either a field or a Cohen ring.  This is the presentation half of the Cohen
structure theorem; the coefficient-subring half is owned by `Completion.CoefficientRing`.

@stack 032A
-/

@[expose] public section

universe u

open IsLocalRing

namespace IsCompleteLocalRing

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R]

/-- Theorem 10.160.8 (Cohen structure theorem): if the maximal ideal of a complete local ring is
finitely generated, the ring is a quotient of a finite-variable power-series ring over a field or
a Cohen ring. -/
@[stacks 032A "(2), power-series quotient presentation"]
theorem exists_mvPowerSeries_quotient (hfg : (maximalIdeal R).FG) :
    ∃ n : ℕ,
      (∃ (k : Type u) (_ : Field k) (I : Ideal (MvPowerSeries (Fin n) k)),
          Nonempty (((MvPowerSeries (Fin n) k) ⧸ I) ≃+* R)) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ)
          (I : Ideal (MvPowerSeries (Fin n) Λ)),
          Nonempty (((MvPowerSeries (Fin n) Λ) ⧸ I) ≃+* R) := sorry

end IsCompleteLocalRing
