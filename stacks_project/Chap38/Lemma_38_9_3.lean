/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Flat.Projective.GeometricallyIntegral
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

/- Lemma 38.9.3: a flat finitely presented algebra with geometrically integral fibres is
projective as a module over the base ring. -/
@[stacks 05FT] #check
  (Module.Projective.ofGeometricallyIntegralOfFinitePresentation :
    ∀ {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [Module.Flat R S]
    [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))],
    Module.Projective R S)
