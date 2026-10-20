module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
import ReasLib.RingTheory.KrullDimension.Relative.QuasiFinite

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally finite-type scheme morphism with fiber dimension `d` at a point admits, over any
affine neighborhood of its image, an affine neighborhood that factors quasi-finitely through
relative affine `d`-space. -/
theorem exists_affineOpen_quasiFinite_to_affineSpace_of_fiberDimensionAt
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (x : X) (d : ℕ) (hfdim : f.fiberDimensionAt x = (d : WithBot ℕ∞))
    (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        let A := AffineSpace (ULift.{u} (Fin d)) ((V : S.Opens).toScheme)
        ∃ π : ((U : X.Opens).toScheme) ⟶ A,
          Scheme.Hom.QuasiFinite π ∧
            π ≫ (A ↘ ((V : S.Opens).toScheme)) = f.resLE (V : S.Opens) (U : X.Opens) e := sorry

end AlgebraicGeometry.Scheme.Hom
