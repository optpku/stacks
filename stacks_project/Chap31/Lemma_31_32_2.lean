/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Affine

universe u

open scoped AlgebraicGeometry

/- Lemma 31.32.2 (1): the inverse image of an affine open under a chosen blowup is canonically
isomorphic to the projective spectrum of the Rees algebra of the corresponding ideal. -/
@[stacks 0804] #check (AlgebraicGeometry.Blowup.preimageAffineOpenIso :
  {X : AlgebraicGeometry.Scheme.{u}} → {I : X.IdealSheafData} →
    (π : AlgebraicGeometry.Blowup X I) → (U : X.affineOpens) →
      (π.hom ⁻¹ᵁ (U : X.Opens)).toScheme ≅
        AlgebraicGeometry.Proj (ReesAlgebra.Grading.grade (I.ideal U)))

/- Lemma 31.32.2 (2): the inverse image of an affine open under a chosen blowup has an affine
open cover by spectra of the corresponding affine blowup algebras. -/
@[stacks 0804] #check (AlgebraicGeometry.Blowup.existsAffineOpenCoverByBlowupCharts :
  {X : AlgebraicGeometry.Scheme.{u}} → {I : X.IdealSheafData} →
    (π : AlgebraicGeometry.Blowup X I) → (U : X.affineOpens) →
      ∃ 𝒰 : ((π.hom ⁻¹ᵁ (U : X.Opens)).toScheme).AffineOpenCover,
        ∀ i : 𝒰.I₀, ∃ a : I.ideal U,
        Nonempty
          (((𝒰.openCover.f i).opensRange).toScheme ≅
            AlgebraicGeometry.Spec (.of (affineBlowupChart (I.ideal U) a))))
