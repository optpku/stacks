/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood

@[expose] public section

open CategoryTheory
open AlgebraicGeometry Scheme
open Scheme.CoherentCompletion

noncomputable section

universe u

set_option allowUnsafeReducibility true in
-- Local declaration justification (localized automation): unfold `Scheme.Opens.toScheme` so typeclass search finds the canonical Noetherian open-restriction instance.
attribute [local reducible] Scheme.Opens.toScheme

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Bijectivity of the endpoint neighborhood comparisons implies bijectivity of the middle comparison in a short exact sequence. -/
theorem middleComparison_bijective_of_left_right
    (setup : AffineAlgebraizationSetup A)
    (F : ShortComplex (RingedSpace.Coh (setup.U.toScheme).toRingedSpace))
    (hF : F.ShortExact)
    (h_left : Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₁.obj))
    (h_right : Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₃.obj)) :
    Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₂.obj) := sorry

/-- Bijectivity of the middle and right neighborhood comparisons implies bijectivity of the left comparison in a short exact sequence. -/
theorem leftComparison_bijective_of_middle_right
    (setup : AffineAlgebraizationSetup A)
    (F : ShortComplex (RingedSpace.Coh (setup.U.toScheme).toRingedSpace))
    (hF : F.ShortExact)
    (h_middle : Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₂.obj))
    (h_right : Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₃.obj)) :
    Function.Bijective (neighborhoodComparison
      ((idealSheafDataOfIdealOnSpec setup.I).comap setup.U.ι) F.X₁.obj) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
