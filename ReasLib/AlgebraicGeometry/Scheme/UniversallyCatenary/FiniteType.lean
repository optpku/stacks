module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.Catenary
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Dedekind
public import ReasLib.RingTheory.Catenary.DimensionOne
public import ReasLib.RingTheory.Catenary.Field

/-!
# Universal catenarity over standard bases

This module records universal-catenarity consequences for schemes locally of finite type over
fields, Cohen-Macaulay schemes, the spectrum of the integers, and spectra of one-dimensional
Noetherian domains.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme locally of finite type over a field is universally catenary. -/
theorem universallyCatenary_of_locallyOfFiniteType_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] :
    UniversallyCatenary X := by
  exact universallyCatenary_of_locallyOfFiniteType f

/-- A scheme locally of finite type over a Cohen-Macaulay scheme is universally catenary. -/
theorem universallyCatenary_of_locallyOfFiniteType_over_cohenMacaulay
    {S X : Scheme.{u}} [Scheme.CohenMacaulay S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    UniversallyCatenary X := by
  exact universallyCatenary_of_locallyOfFiniteType f

/-- A scheme locally of finite type over the spectrum of the integers is universally catenary. -/
theorem universallyCatenary_of_locallyOfFiniteType_over_specInt
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    UniversallyCatenary X := by
  exact universallyCatenary_of_locallyOfFiniteType f

/-- A scheme locally of finite type over the spectrum of a one-dimensional Noetherian domain is
universally catenary. -/
theorem UniversallyCatenary.of_dimOneDomain
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    UniversallyCatenary X := by
  -- Local instance justification (proof-local temporary data): the explicit dimension equality supplies universal catenarity of this proof's base ring.
  letI : UniversallyCatenaryRing.{u, u} R :=
    UniversallyCatenaryRing.of_isDomain_ringKrullDim_eq_one hdim
  exact universallyCatenary_of_locallyOfFiniteType f

end AlgebraicGeometry
