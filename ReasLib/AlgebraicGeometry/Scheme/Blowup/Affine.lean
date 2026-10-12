/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
public import ReasLib.RingTheory.ReesAlgebra.BlowupChart

/-!
# Affine charts of blowups

This file identifies the inverse image of an affine open under a chosen blowup with the
projective spectrum of its Rees algebra and records the resulting affine blowup-chart cover.
-/

@[expose] public section

namespace AlgebraicGeometry

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

variable {X : Scheme.{u}} {I : X.IdealSheafData}

namespace Blowup

/-- The inverse image of an affine open under a chosen blowup is canonically isomorphic to the
projective spectrum of the Rees algebra of the corresponding ideal of sections. -/
def preimageAffineOpenIso (π : Blowup X I) (U : X.affineOpens) :
    (π.hom ⁻¹ᵁ (U : X.Opens)).toScheme ≅
      Proj (ReesAlgebra.Grading.grade (I.ideal U)) :=
  π.reesPresentation.affineOpenIso U

/-- The inverse image of an affine open under a chosen blowup has an affine open cover whose
members are spectra of the affine blowup charts of the corresponding ideal of sections. -/
theorem existsAffineOpenCoverByBlowupCharts (π : Blowup X I) (U : X.affineOpens) :
    ∃ 𝒰 : ((π.hom ⁻¹ᵁ (U : X.Opens)).toScheme).AffineOpenCover,
      ∀ i : 𝒰.I₀, ∃ a : I.ideal U,
        Nonempty
          (((𝒰.openCover.f i).opensRange).toScheme ≅
            Spec (.of (affineBlowupChart (I.ideal U) a))) := sorry

end Blowup

end

end AlgebraicGeometry
