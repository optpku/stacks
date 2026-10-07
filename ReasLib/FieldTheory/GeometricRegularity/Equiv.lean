module

public import ReasLib.FieldTheory.GeometricRegularity

@[expose] public section

/-!
# Geometric regularity and algebra equivalences

@stack 0382

Geometric regularity is intrinsic to a field algebra, so consumers should not
rebuild tensor-product transports whenever they change to an equivalent model.
-/

namespace Algebra

universe u v w

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- Geometric regularity is invariant under an equivalence of field algebras. -/
@[stacks 0382 "geometric regularity under algebra equivalence"]
theorem isGeometricallyRegular_algEquiv_iff (e : A ≃ₐ[k] B) :
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k B := sorry

/-- Transport geometric regularity backwards along an equivalence of field algebras. -/
theorem isGeometricallyRegular_of_algEquiv (e : A ≃ₐ[k] B)
    [IsGeometricallyRegular k B] : IsGeometricallyRegular k A := sorry

end Algebra
