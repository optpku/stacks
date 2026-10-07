module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.Localization.Away.Basic

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.FpTAwayAffineLine

/-- The polynomial ring `Polynomial (ZMod p)`, corresponding to the coordinate ring of
`Spec (Polynomial (ZMod p))`. -/
abbrev baseRing (p : ℕ) [Fact p.Prime] : Type :=
  Polynomial (ZMod p)

/-- The polynomial ring `Polynomial (baseRing p)`, corresponding to `(ZMod p)[t][x]`
before inverting `denom p`. -/
abbrev ambientRing (p : ℕ) [Fact p.Prime] : Type :=
  Polynomial (Polynomial (ZMod p))

/-- The inverted element `x * (x - t) * (t * x - 1)` in `ambientRing p`, where `x` is
`Polynomial.X` and `t` is `Polynomial.C Polynomial.X`. -/
def denom (p : ℕ) [Fact p.Prime] : ambientRing p :=
  Polynomial.X * (Polynomial.X - Polynomial.C Polynomial.X) *
    (Polynomial.C Polynomial.X * Polynomial.X - 1)

/-- The coordinate ring obtained by inverting `denom p` in `ambientRing p`. -/
abbrev coordRing (p : ℕ) [Fact p.Prime] : Type :=
  Localization.Away (denom p)

/-- The base scheme `Spec (baseRing p)`. -/
abbrev base (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (baseRing p))

/-- The localized affine scheme `Spec (coordRing p)`. -/
abbrev total (p : ℕ) [Fact p.Prime] : Scheme :=
  Spec (CommRingCat.of (coordRing p))

/-- The structure map `baseRing p →+* coordRing p` obtained by inserting coefficients via
`Polynomial.C` and then localizing away from `denom p`. -/
def structureRingHom (p : ℕ) [Fact p.Prime] : baseRing p →+* coordRing p :=
  (algebraMap (ambientRing p) (coordRing p)).comp Polynomial.C

/-- The morphism `total p ⟶ base p` induced by `structureRingHom p`. -/
def toBase (p : ℕ) [Fact p.Prime] : total p ⟶ base p :=
  Spec.map (CommRingCat.ofHom (structureRingHom p))

/-- For a prime `p`, the affine scheme with coordinate ring `(ZMod p)[t][x]` localized
at `x * (x - t) * (t * x - 1)` contains a closed subscheme finite and surjective over
`Spec (Polynomial (ZMod p))` under its structural morphism. -/
theorem exists_isClosedImmersion_isFinite_surjective (p : ℕ) [Fact p.Prime] :
    ∃ (Z : Scheme) (i : Z ⟶ total p),
      IsClosedImmersion i ∧ IsFinite (i ≫ toBase p) ∧ Surjective (i ≫ toBase p) := sorry

end AlgebraicGeometry.FpTAwayAffineLine
