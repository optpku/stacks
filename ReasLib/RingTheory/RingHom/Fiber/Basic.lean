/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Fiber.Map

@[expose] public section

/-!
# Basic Fiber Properties of Ring Homomorphisms

The reduced-fibers property requires every residue-field fiber of a
commutative-ring homomorphism to be reduced. A bound on fiber dimension
requires every such fiber to have Krull dimension at most the specified
natural number.
-/

universe u v

namespace RingHom

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- A ring map has reduced fibers when every residue-field fiber over a prime
of its source is reduced. -/
@[stacks 01SX "(3)"]
def HasReducedFibers (phi : R →+* A) : Prop :=
  forall p : PrimeSpectrum R, IsReduced (phi.Fiber p.asIdeal)

/-- A ring map has fibers of Krull dimension at most `n` when every
residue-field fiber over a prime of its source has that bound. -/
@[stacks 01SX "(4)"]
def FibersKrullDimLE (n : Nat) (phi : R →+* A) : Prop :=
  forall p : PrimeSpectrum R, Ring.KrullDimLE n (phi.Fiber p.asIdeal)

namespace HasReducedFibers

/-- A reduced-fibers hypothesis supplies reducedness of the fiber over any
chosen source prime. -/
theorem isReduced {phi : R →+* A} (h : HasReducedFibers (R := R) (A := A) phi)
    (p : PrimeSpectrum R) :
    IsReduced (phi.Fiber p.asIdeal) := sorry

end HasReducedFibers

namespace FibersKrullDimLE

/-- A fiber-dimension bound supplies the corresponding bound over any chosen
source prime. -/
theorem krullDimLE {n : Nat} {phi : R →+* A}
    (h : FibersKrullDimLE (R := R) (A := A) n phi) (p : PrimeSpectrum R) :
    Ring.KrullDimLE n (phi.Fiber p.asIdeal) := sorry

end FibersKrullDimLE

end

section

variable {R A : Type u} [CommRing R] [CommRing A]

namespace HasReducedFibers

/-- Having reduced fibers is a local property of a commutative ring map. -/
@[stacks 01SX "(3)"]
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.HasReducedFibers := sorry

end HasReducedFibers

namespace FibersKrullDimLE

/-- A fixed upper bound on the Krull dimensions of fibers is a local property
of a commutative ring map. -/
@[stacks 01SX "(4)"]
theorem propertyIsLocal (n : Nat) :
    RingHom.PropertyIsLocal (RingHom.FibersKrullDimLE n) := sorry

end FibersKrullDimLE

end

end RingHom
