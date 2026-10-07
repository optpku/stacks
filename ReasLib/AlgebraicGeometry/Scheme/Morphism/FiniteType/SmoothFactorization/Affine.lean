module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.SmoothFactorization.GeometricallyIntegral

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite type morphism whose fibre has dimension `n` at `x` admits affine
elementary étale neighbourhoods of `x` and `f x` and a finite factorization through an
affine scheme and a smooth morphism of relative dimension `n` with geometrically integral
fibres. The distinguished fibre is a singleton, its residue-field extension is purely
transcendental, and the finite map is of finite presentation whenever the original morphism
is locally of finite presentation. -/
theorem exists_affine_finite_smoothFactorization_geometricallyIntegral {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) (n : ℕ)
    (h_dim : f.fiberDimensionAt x = (n : WithBot ℕ∞)) :
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
            LocallyOfFinitePresentation f → Scheme.Hom.FinitePresentation π := sorry

end AlgebraicGeometry.Scheme.Hom
