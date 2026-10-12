/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Kollar

/-!
# Kollar's determinantal local data

This leaf owns the local determinantal data used to construct Kollar's
exceptional finite extension.  It is stated independently of the Chapter 10
presentation so later applications can import it directly.
-/

@[expose] public section

universe u

namespace IsLocalRing.Kollar.Determinantal

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R] [IsNoetherianRing R]

/-- A one-dimensional nonregular Noetherian local domain has a regular element `x` in its
maximal ideal and a ratio numerator `y` with the determinantal maximal-ideal relation. -/
@[stacks 0BHZ "Kollar determinantal local data"]
theorem exists_ratio
    (hdim : ringKrullDim R = 1) (hregular : ¬ IsRegularLocalRing R) :
    ∃ x y : R,
      x ∈ maximalIdeal R ∧
        IsSMulRegular R x ∧
          y ∉ Ideal.span ({x} : Set R) ∧
            ∀ t ∈ maximalIdeal R, ∃ s ∈ maximalIdeal R, y * t = x * s := sorry

end IsLocalRing.Kollar.Determinantal
