module

public import ReasLib.RingTheory.Flat.Projective.GeometricallyIntegral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

/- Lemma 38.9.2: a finite-type flat algebra with geometrically integral fibres over a
Noetherian ring is projective as a module over the base ring. -/
@[stacks 05FS] #check
  (Module.Projective.ofGeometricallyIntegral :
    ∀ {R S : Type u}, [CommRing R] → [CommRing S] → [Algebra R S] →
      [IsNoetherianRing R] → [Algebra.FiniteType R S] → [Module.Flat R S] →
      [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))] →
      Module.Projective R S)
