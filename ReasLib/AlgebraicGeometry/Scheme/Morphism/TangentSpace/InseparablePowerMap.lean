module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.InseparablePowerMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace.EmbeddingDimension

/-!
# Tangent dimensions of inseparable p-power morphisms

The relative tangent spaces of the p-power morphisms of rational-function
fields and affine lines are one-dimensional in characteristic `p`.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.InseparablePowerMap

/-- The relative tangent space of `hom p` at the unique point is
finite-dimensional over the residue field. -/
instance instFiniteDimensionalFunctionFieldTangentSpace (p : ℕ) [Fact p.Prime] :
    FiniteDimensional ((scheme p).residueField default)
      (tangentSpaceAt (hom p) default) := sorry

/-- The relative tangent space of `affineLineHom p` is finite-dimensional over
the residue field at every point. -/
instance instFiniteDimensionalAffineLineTangentSpace (p : ℕ) [Fact p.Prime]
    (x : affineLine p) :
    FiniteDimensional ((affineLine p).residueField x)
      (tangentSpaceAt (affineLineHom p) x) := sorry

/-- The relative tangent space of the p-power morphism on `Spec (𝔽_p(t))`
has dimension one at its unique point. -/
theorem tangentDimension_eq_one (p : ℕ) [Fact p.Prime] :
    tangentDimensionAt (hom p) default = 1 := sorry

/-- The relative tangent space of the p-power morphism on `Spec (𝔽_p[t])`
has dimension one at every point. -/
theorem affineLine_tangentDimension_eq_one (p : ℕ) [Fact p.Prime]
    (x : affineLine p) :
    tangentDimensionAt (affineLineHom p) x = 1 := sorry

end AlgebraicGeometry.InseparablePowerMap
