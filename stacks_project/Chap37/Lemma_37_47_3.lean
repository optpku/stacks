/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.SmoothFactorization.Affine
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.47.3: the elementary étale neighbourhoods and finite factorization of
`exists_finite_smoothFactorization_geometricallyIntegral` can be chosen so that the
underlying source and base schemes and the intermediate scheme are all affine. -/
@[stacks 057L] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affine_finite_smoothFactorization_geometricallyIntegral :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ)
      (h_dim : f.fiberDimensionAt x = (n : WithBot ℕ∞)),
      ∃ U : EtaleNeighborhood.Elementary X x,
        let X' := U.obj
        let x' := X'.point
        ∃ (_ : IsAffine X'.toEtale.left) (V : EtaleNeighborhood.Elementary S (f x)),
          let S' := V.obj
          ∃ (_ : IsAffine S'.toEtale.left) (Y' : Scheme.{u}) (_ : IsAffine Y')
            (π : X'.toEtale.left ⟶ Y') (h : Y' ⟶ S'.toEtale.left),
            let y' := π x'
            let s' := h y'
            ∃ (_ : X'.toEtale.hom ≫ f = π ≫ h ≫ S'.toEtale.hom)
              (_ : s' = S'.point)
              (_ : SmoothOfRelativeDimension n h)
              (_ : GeometricallyIntegral h)
              (_ : IsFinite π)
              (_ : π ⁻¹' {y'} = {x'})
              (_ : (h.residueFieldMap y').hom.IsPurelyTranscendental),
              LocallyOfFinitePresentation f → Scheme.Hom.FinitePresentation π)

end AlgebraicGeometry.Scheme.Hom
