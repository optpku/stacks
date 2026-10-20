/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Flat
public import stacks_project.Chap38.Lemma_38_9_3
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S]
variable [GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))]

/- Remark 38.9.4: if R → S is smooth with geometrically integral fibres,
then S is projective as an R-module. -/
@[stacks 05FU] #check
  (Module.Projective.ofGeometricallyIntegralOfFinitePresentation : Module.Projective R S)
