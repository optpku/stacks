module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.Spectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Alteration

/-!
# Dimension bounds for special fibres over local domains
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is a modification of algebraic spaces,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
theorem dimension_specialFiber_le_of_isModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A)
    [IsModification f] :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is an alteration of algebraic spaces,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
theorem dimension_specialFiber_le_of_isAlteration
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A)
    [IsAlteration f] :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is locally of finite type and
quasi-separated, `X` is integral, and there is exactly one point of `Points X`
mapping to the generic point of `specSpace A`, then
`dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
theorem dimension_specialFiber_le_of_unique_genericPoint_preimage
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsIntegral X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    [QuasiSeparated f]
    (hη : ∃! x : Points X, Points.map f x = specSpaceGenericPoint A) :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

/-- Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension
at least `1`. If `f : X ⟶ specSpace A` is locally of finite type, `X` is
decent, and the points of `Points X` mapping to the generic point of
`specSpace A` are the generic points of irreducible components of `Points X`,
then `dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1)`. -/
theorem dimension_specialFiber_le_of_genericPoint_preimage_eq_genericPoints
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (hdim : 1 ≤ ringKrullDim A) {X : AlgebraicSpace (Spec (.of A))}
    [IsDecent X] (f : X ⟶ specSpace A) [LocallyOfFiniteType f]
    (hη : Points.map f ⁻¹' {specSpaceGenericPoint A} = genericPoints X) :
    dimension (fiber f (IsLocalRing.closedPoint A)) ≤ (ringKrullDim A).map (· - 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
