/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Cancellation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism.Radicial

/-!
# Properties of absolute and relative Frobenius

This leaf gathers the standard universal-homeomorphism, integrality,
pure-inseparability, and finite-type consequences of Frobenius morphisms.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

variable {p : ℕ} [Fact p.Prime]
variable {X : Scheme.{u}} [Scheme.IsCharP X p]

/-- The absolute Frobenius of a scheme of prime characteristic is a universal
homeomorphism. -/
@[stacks 0CC8]
instance absoluteFrobenius_universalHomeomorphism :
    UniversalHomeomorphism (Scheme.absoluteFrobenius p X) := sorry

/-- The absolute Frobenius of a scheme of prime characteristic is integral. -/
@[stacks 0CC8]
instance absoluteFrobenius_isIntegralHom :
    IsIntegralHom (Scheme.absoluteFrobenius p X) := sorry

/-- The absolute Frobenius of a scheme of prime characteristic induces purely inseparable
extensions on residue fields. -/
@[stacks 0CC8]
instance absoluteFrobenius_residueField_isPurelyInseparable (x : X) :
    IsPurelyInseparable
      (X.residueField ((Scheme.absoluteFrobenius p X) x))
      (X.residueField x) := sorry

end

namespace Scheme.Hom

section

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The relative Frobenius of a scheme morphism in prime characteristic is a universal
homeomorphism. -/
@[stacks 0CCB]
instance relativeFrobenius_universalHomeomorphism :
    UniversalHomeomorphism (relativeFrobenius (p := p) f) := sorry

/-- The relative Frobenius of a scheme morphism in prime characteristic is integral. -/
@[stacks 0CCB]
instance relativeFrobenius_isIntegralHom :
    IsIntegralHom (relativeFrobenius (p := p) f) := sorry

/-- The relative Frobenius of a scheme morphism in prime characteristic induces purely
inseparable extensions on residue fields. -/
@[stacks 0CCB]
instance relativeFrobenius_residueField_isPurelyInseparable (x : X) :
    IsPurelyInseparable
      ((relativeFrobeniusTarget (p := p) f).residueField
        ((relativeFrobenius (p := p) f) x))
      (X.residueField x) := sorry

end

section

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/-- The relative Frobenius of a locally finite type scheme morphism in prime characteristic
is finite. -/
@[stacks 0CCD]
instance relativeFrobenius_isFinite [LocallyOfFiniteType f] :
    IsFinite (relativeFrobenius (p := p) f) := sorry

end

end Scheme.Hom
end AlgebraicGeometry
