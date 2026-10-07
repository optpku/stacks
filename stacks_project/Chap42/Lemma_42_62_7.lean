module

public import stacks_project.Chap42.Lemma_42_62_7_Comparison

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual
open scoped Topology TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- Lemma 42.62.7: Let `k` be a field. Let `X` be a smooth scheme over `k` which is
quasi-compact and has affine diagonal. Then the intersection product on `CH^*(X)`
constructed in this section agrees after tensoring with `ℚ` with the intersection
product constructed in Section 42.58.

After identifying `CH^*(X) ⊗ ℚ` with `rationalChow` via the usual
dimension/codimension reindexing, the Section 42.62 product of
`chernCapFundamental` images equals the Section 42.58 product
`rationalIntersectionProduct`. -/
@[stacks 0FFF]
theorem intersectionProduct_eq_rationalIntersectionProduct
    (X : SchemeOverField k) [Smooth X.hom] [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    (r : ℕ) [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r) (hdim : topologicalKrullDim X.left < ⊤)
    (classes : ChernClass.Theory (fun _ ↦ 0) X.hom)
    (α' β' : TensorProduct ℤ (Scheme.VectorBundleK0 X.left) ℚ) :
    intersectionProductRational X r D
        (chernCapFundamental (fun _ ↦ 0) X classes hdim α')
        (chernCapFundamental (fun _ ↦ 0) X classes hdim β') =
      rationalIntersectionProduct (fun _ ↦ 0) X classes hdim α' β' := sorry

end AlgebraicGeometry.ChowGroup
