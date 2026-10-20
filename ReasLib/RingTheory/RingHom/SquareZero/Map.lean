module

public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Bundled square-zero ring maps

A square-zero ring map is a surjective homomorphism of commutative rings whose
kernel has square zero.
-/

@[expose] public section

universe u v

namespace RingHom.SquareZeroExtension

/-- Ring homomorphisms that are surjective with square-zero kernel. -/
abbrev Map (R : Type u) (A : Type v) [CommRing R] [CommRing A] :=
  {f : R →+* A // f.IsSquareZeroExtension}

namespace Map

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

/-- Bundle a ring homomorphism with its square-zero extension property. -/
def of (f : R →+* A) [h : f.IsSquareZeroExtension] : Map R A := ⟨f, h⟩

/-- The underlying homomorphism of a square-zero ring map. -/
abbrev hom (f : Map R A) : R →+* A := f.val

/-- The underlying homomorphism is a square-zero extension. -/
instance isSquareZero (f : Map R A) : f.hom.IsSquareZeroExtension := f.property

end Map

end RingHom.SquareZeroExtension
