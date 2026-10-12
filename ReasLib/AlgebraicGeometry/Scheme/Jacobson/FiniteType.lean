/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Jacobson.IdealComplement
public import ReasLib.RingTheory.Jacobson.Noetherian

/-!
# Jacobson schemes locally of finite type

Schemes locally of finite type over standard Jacobson bases are Jacobson.
-/

@[expose] public section

open AlgebraicGeometry PrimeSpectrum IsLocalRing
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyOfFiniteType

/-- A scheme locally of finite type over a field is Jacobson. -/
theorem jacobsonSpace_over_field
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/-- A scheme locally of finite type over the spectrum of the integers is Jacobson. -/
theorem jacobsonSpace_over_integers
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℤ)) [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/-- A scheme locally of finite type over the spectrum of a one-dimensional Noetherian domain
with infinite prime spectrum is Jacobson. -/
theorem jacobsonSpace_over_spec_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [Infinite (PrimeSpectrum R)] (hdim : ringKrullDim R = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

/-- A scheme locally of finite type over the punctured spectrum of a Noetherian local ring is
Jacobson. -/
theorem jacobsonSpace_over_puncturedSpectrum
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ PuncturedSpectrum.scheme A) [LocallyOfFiniteType f] :
    JacobsonSpace X := sorry

end AlgebraicGeometry.LocallyOfFiniteType
