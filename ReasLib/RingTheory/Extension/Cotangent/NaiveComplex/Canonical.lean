module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Canonical naive cotangent complexes

The presentation-level owner is `Algebra.Extension.NaiveCotangent.complex`.  This file selects the
canonical self-presentation of an algebra and packages the resulting construction for bundled
commutative-ring morphisms.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace Algebra

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical naive cotangent complex of an `R`-algebra `S`, obtained
from the self-presentation of `S`. -/
@[stacks 07BN "canonical self-presentation"]
abbrev naiveCotangent : ChainComplex (ModuleCat S) ℕ :=
  Extension.NaiveCotangent.complex (Generators.self R S).toExtension

end Algebra

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical naive cotangent complex attached directly to a commutative-ring
homomorphism. -/
@[stacks 07BN "ring-homomorphism view"]
noncomputable abbrev naiveCotangent (f : R →+* S) :
    ChainComplex (ModuleCat S) ℕ :=
  @Algebra.naiveCotangent R S _ _ f.toAlgebra

end RingHom

namespace CommRingCat.Hom

variable {R S : CommRingCat.{u}}

/-- The canonical naive cotangent complex attached to a bundled commutative-ring morphism. -/
@[stacks 07BN "bundled ring morphism view"]
noncomputable abbrev naiveCotangent (f : R ⟶ S) :
    ChainComplex (ModuleCat S) ℕ :=
  RingHom.naiveCotangent f.hom

end CommRingCat.Hom

namespace NaiveCotangent

/-- Notation for the canonical naive cotangent complex of an algebra. -/
scoped notation "NL{" S "⁄" R "}" => Algebra.naiveCotangent R S

/-- Notation for the canonical naive cotangent complex of a bundled ring morphism. -/
scoped notation:max "NL(" f ")" => CommRingCat.Hom.naiveCotangent f

end NaiveCotangent
