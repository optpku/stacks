module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Affine
import StacksCheckRecall

universe u

/- Lemma 30.2.2: let `X` be a scheme and let `ℱ` be a quasi-coherent `𝒪_X`-module.
For any affine open `U ⊆ X`, the higher cohomology groups `H^p(U, ℱ)` vanish for all
`p > 0`. -/
@[stacks 01XB] #check
  (AlgebraicGeometry.Scheme.higherCohomology_isZero_on_affineOpen :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (U : X.Opens) (_ : AlgebraicGeometry.IsAffineOpen U) (p : ℕ), 0 < p →
        CategoryTheory.Limits.IsZero
          (((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).H' p U))
