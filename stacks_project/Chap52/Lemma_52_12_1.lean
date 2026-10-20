/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.ShortExact
import StacksCheckRecall

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] AlgebraicGeometry.Scheme.Opens.toScheme

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/- Lemma 52.12.1 (1): for a short exact sequence of coherent modules on
`Spec(A) ∖ V(setup.a)`, bijectivity of the canonical neighborhood-to-completion comparisons
for the left and right terms implies bijectivity for the middle term. -/
@[stacks 0H48] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.middleComparison_bijective_of_left_right :
    ∀ (setup : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (F : CategoryTheory.ShortComplex
        (AlgebraicGeometry.RingedSpace.Coh (setup.U.toScheme).toRingedSpace)),
      F.ShortExact →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₁.obj) →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₃.obj) →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₂.obj))

/- Lemma 52.12.1 (2): the source wording appears self-referential; the proof-intended
noncircular reading uses bijectivity of the middle and right comparisons to imply bijectivity
of the left comparison. -/
@[stacks 0H48] #check
  (AlgebraicGeometry.AffineAlgebraizationSetup.leftComparison_bijective_of_middle_right :
    ∀ (setup : AlgebraicGeometry.AffineAlgebraizationSetup A)
      (F : CategoryTheory.ShortComplex
        (AlgebraicGeometry.RingedSpace.Coh (setup.U.toScheme).toRingedSpace)),
      F.ShortExact →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₂.obj) →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₃.obj) →
      Function.Bijective (AlgebraicGeometry.Scheme.CoherentCompletion.neighborhoodComparison
        ((AlgebraicGeometry.Scheme.idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι)
        F.X₁.obj))
