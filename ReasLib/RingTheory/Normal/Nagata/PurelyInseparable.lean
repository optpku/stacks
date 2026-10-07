module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Nagata

@[expose] public section

/-!
# Purely Inseparable Tests for Japanese Domains

@stack 032N

This module records the positive-characteristic criterion which tests the
`N-2` condition on finite purely inseparable extensions of the fraction field.
-/

universe u

namespace IsN2Ring

variable {R : Type u}

/-- Lemma 10.161.12, tag `032N`: a Noetherian domain with fraction field of
characteristic `p > 0` is `N-2` exactly when its integral closures in all finite purely
inseparable fraction-field extensions are finite. -/
@[stacks 032N]
theorem iff_forall_finitePurelyInseparable
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing R) p] :
    IsN2Ring R ↔
      ∀ (L : Type u) [Field L] [Algebra R L] [Algebra (FractionRing R) L]
        [IsScalarTower R (FractionRing R) L] [FiniteDimensional (FractionRing R) L]
        [IsPurelyInseparable (FractionRing R) L],
        Module.Finite R (integralClosure R L) := sorry

end IsN2Ring
