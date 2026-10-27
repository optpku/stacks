/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Total
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Regular
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Canonical
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.Regularity

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

variable {k : Type u} [Field k]

/-- On Chern-character cap images, rationalized smooth intersection equals the product
represented by multiplication of rational vector-bundle classes. -/
theorem smoothIntersectionProductRational_chernCapFundamental (X : SchemeOverField k)
    [Smooth X.hom] [CompactSpace X.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    (α' β' : Scheme.VectorBundleK0 X.left ⊗[ℤ] ℚ) :
    smoothIntersectionProductRational X
        (chernCapFundamental (fun _ ↦ 0) X (ChernClass.Theory.canonical (fun _ ↦ 0) X.hom)
          (SchemeOverField.topologicalKrullDim_lt_top X) α')
        (chernCapFundamental (fun _ ↦ 0) X (ChernClass.Theory.canonical (fun _ ↦ 0) X.hom)
          (SchemeOverField.topologicalKrullDim_lt_top X) β') =
      rationalIntersectionProduct (fun _ ↦ 0) X
        (ChernClass.Theory.canonical (fun _ ↦ 0) X.hom)
        (SchemeOverField.topologicalKrullDim_lt_top X) α' β' := sorry

/-- On a quasi-compact smooth scheme over a field with affine diagonal, the smooth
intersection product extended to rational Chow homology agrees with the regular
intersection product defined by the canonical Chern-character cap equivalence. -/
theorem smoothIntersectionProductRational_eq_regularIntersectionProduct (X : SchemeOverField k)
    [Smooth X.hom] [CompactSpace X.left]
    [IsAffineHom (prod.lift (𝟙 X.left) (𝟙 X.left))]
    (α β : rationalChow (fun _ ↦ 0) X) :
    smoothIntersectionProductRational X α β =
      regularIntersectionProduct (fun _ ↦ 0) X
        (ChernClass.Theory.canonical (fun _ ↦ 0) X.hom)
        (SchemeOverField.topologicalKrullDim_lt_top X) α β := sorry

end AlgebraicGeometry.ChowGroup
