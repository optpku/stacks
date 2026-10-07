module

public import stacks_project.Chap111.Exercise_111_35_8_PowerMap
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.TangentSpace
import Mathlib.Tactic.CrossRefAttribute

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

/-- Exercise 111.35.8 (1): the relative tangent space of
`X = Spec (𝔽_p(t)) ⟶ Spec (𝔽_p(t^p)) = S` at the unique point of `X` is
1-dimensional over the residue field. -/
@[stacks 029J]
theorem tangentDimension_eq_one (p : ℕ) [Fact p.Prime] :
    tangentDimensionAt (hom p) default = 1 := sorry

/-- Exercise 111.35.8 (2): the relative tangent space of the morphism
corresponding to `𝔽_p[t^p] → 𝔽_p[t]` is 1-dimensional at every point of
`Spec (𝔽_p[t])`. -/
@[stacks 029J]
theorem affineLine_tangentDimension_eq_one (p : ℕ) [Fact p.Prime]
    (x : affineLine p) :
    tangentDimensionAt (affineLineHom p) x = 1 := sorry

end AlgebraicGeometry.InseparablePowerMap
