/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.CohomologicalDimension
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 51.4.11: if every fibre of the blowup of `Spec A` in `I` has dimension
strictly less than `d`, then local cohomology with support in `I` has dimension at most `d`. -/
@[stacks 0EHU] #check (Ideal.LocalCohomology.hasDimensionLE_of_blowup :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X' : Scheme.{u}} (b : X' ⟶ Spec (CommRingCat.of A))
    [IsBlowup b (Scheme.idealSheafDataOfIdealOnSpec I)] (d : ℕ)
    (hdim : ∀ x : Spec (CommRingCat.of A),
      b.fiberDimension x < (d : WithBot ℕ∞)),
    Ideal.LocalCohomology.HasDimensionLE I (d : ℤ))
