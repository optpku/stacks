/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.RingTheory.AdicCompletion.Projective

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

namespace Module.Projective

/-- A finite-type flat algebra with geometrically integral fibers over a Noetherian ring is
projective as a module over the base ring. -/
instance ofGeometricallyIntegral
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] :
    Module.Projective R S := sorry

/-- A flat finitely presented algebra with geometrically integral fibers is projective as a
module over the base ring. -/
instance ofGeometricallyIntegralOfFinitePresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] :
    Module.Projective R S := sorry

end Module.Projective
