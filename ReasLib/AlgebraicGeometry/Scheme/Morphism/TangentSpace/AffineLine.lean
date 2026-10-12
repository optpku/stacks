/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.EmbeddingDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- Residue fields of the affine line over a field `k` are canonically `k`-algebras
via the structure morphism `affineSpaceOverFieldHom k 1`. -/
noncomputable instance instAlgebraResidueFieldAffineLine
    (x : AffineSpaceOverField k 1) :
    Algebra k ((AffineSpaceOverField k 1).residueField x) :=
  ResidueField.algebraOfSpec (affineSpaceOverFieldHom k 1) x

/-- The relative tangent dimension of the affine line over its base field is `1`
at every closed point. -/
theorem tangentDimensionAt_affineLine_closedPoint
    (x : AffineSpaceOverField k 1) (hx : IsClosed {x}) :
    tangentDimensionAt (affineSpaceOverFieldHom k 1) x = 1 := sorry

/-- The relative tangent dimension of the affine line over its base field is `1`
at its generic point. -/
theorem tangentDimensionAt_affineLine_genericPoint :
    tangentDimensionAt (affineSpaceOverFieldHom k 1)
      (genericPoint (AffineSpaceOverField k 1)) = 1 := sorry

/-- At a closed point `x` of the affine line over `k`, the residue-field rank of
the tangent space over `Spec ℤ` is `1` plus the residue-field rank of
`Ω[k⁄ℤ] →ₗ[k] (AffineSpaceOverField k 1).residueField x`. -/
theorem rank_tangentSpaceAt_affineLine_overInt_closedPoint
    (x : AffineSpaceOverField k 1) (hx : IsClosed {x}) :
    Module.rank ((AffineSpaceOverField k 1).residueField x)
        (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1)) x) =
      1 + Module.rank ((AffineSpaceOverField k 1).residueField x)
        (Ω[k⁄ℤ] →ₗ[k] (AffineSpaceOverField k 1).residueField x) := sorry

/-- At the generic point of the affine line over `k`, the residue-field rank of
the tangent space over `Spec ℤ` is `1` plus the residue-field rank of the
`k`-linear maps from `Ω[k⁄ℤ]` to that residue field. -/
theorem rank_tangentSpaceAt_affineLine_overInt_genericPoint :
    Module.rank
        ((AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1)))
        (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1))
          (genericPoint (AffineSpaceOverField k 1))) =
      1 + Module.rank
        ((AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1)))
        (Ω[k⁄ℤ] →ₗ[k]
          (AffineSpaceOverField k 1).residueField (genericPoint (AffineSpaceOverField k 1))) := sorry

/-- For the affine line over a field, the relative tangent dimension differs
from the absolute tangent-space rank whenever the additional Kähler rank is
nonzero. -/
theorem tangentDimensionAt_affineLine_ne_rank_overInt
    {k : Type u} [Field k] (x : AffineSpaceOverField k 1)
    (hΩ :
      Module.rank ((AffineSpaceOverField k 1).residueField x)
          (Ω[k⁄ℤ] →ₗ[k] (AffineSpaceOverField k 1).residueField x) ≠ 0) :
    (tangentDimensionAt (affineSpaceOverFieldHom k 1) x : Cardinal) ≠
      Module.rank ((AffineSpaceOverField k 1).residueField x)
        (tangentSpaceAt (terminal.from (AffineSpaceOverField k 1)) x) := sorry

end AlgebraicGeometry
