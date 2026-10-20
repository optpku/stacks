/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Reduced.Product
public import ReasLib.AlgebraicGeometry.Scheme.Reduction.Over

/-!
# Reduction of group schemes over perfect fields

The reduction of a group scheme over a perfect field inherits its group
operations by the universal property of reduction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonoidalCategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Over

variable {k : Type u} [Field k] [PerfectField k]
variable (G : Over (Spec (.of k))) [GrpObj G]

/-- The monoidal unit over a field has reduced underlying scheme. -/
instance instIsReducedTensorUnit :
    IsReduced ((𝟙_ (Over (Spec (.of k)))).left) := sorry

/-- The tensor square of the reduction of a group scheme over a perfect field is reduced. -/
instance instIsReducedReductionTensor :
    IsReduced ((reduction G ⊗ reduction G).left) := sorry

/-- The unit of the group structure induced on the reduction. -/
noncomputable def reductionOne :
    𝟙_ (Over (Spec (.of k))) ⟶ reduction G :=
  Hom.reductionLift η[G]

/-- The unit on the reduction followed by its inclusion is the original unit. -/
theorem reductionOne_comp_reductionι :
    reductionOne G ≫ reductionι G = η[G] := sorry

/-- The multiplication of the group structure induced on the reduction. -/
noncomputable def reductionMul :
    reduction G ⊗ reduction G ⟶ reduction G :=
  Hom.reductionLift ((reductionι G ⊗ₘ reductionι G) ≫ μ[G])

/-- Multiplication on the reduction followed by its inclusion is the original multiplication. -/
theorem reductionMul_comp_reductionι :
    reductionMul G ≫ reductionι G =
      (reductionι G ⊗ₘ reductionι G) ≫ μ[G] := sorry

/-- The inverse of the group structure induced on the reduction. -/
noncomputable def reductionInv : reduction G ⟶ reduction G :=
  reductionMap ι[G]

/-- Inversion on the reduction commutes with its inclusion. -/
theorem reductionInv_comp_reductionι :
    reductionInv G ≫ reductionι G = reductionι G ≫ ι[G] := sorry

/-- The left unit law for the induced operations on the reduction. -/
theorem reductionOneMul :
    reductionOne G ▷ reduction G ≫ reductionMul G =
      (λ_ (reduction G)).hom := sorry

/-- The right unit law for the induced operations on the reduction. -/
theorem reductionMulOne :
    reduction G ◁ reductionOne G ≫ reductionMul G =
      (ρ_ (reduction G)).hom := sorry

/-- The associativity law for multiplication on the reduction. -/
theorem reductionMulAssoc :
    (reductionMul G ▷ reduction G) ≫ reductionMul G =
      (α_ (reduction G) (reduction G) (reduction G)).hom ≫
        (reduction G ◁ reductionMul G) ≫ reductionMul G := sorry

/-- The left inverse law for the induced operations on the reduction. -/
theorem reductionLeftInv :
    lift (reductionInv G) (𝟙 (reduction G)) ≫ reductionMul G =
      toUnit (reduction G) ≫ reductionOne G := sorry

/-- The right inverse law for the induced operations on the reduction. -/
theorem reductionRightInv :
    lift (𝟙 (reduction G)) (reductionInv G) ≫ reductionMul G =
      toUnit (reduction G) ≫ reductionOne G := sorry

/-- The canonical group-object structure on the reduction of a group scheme over a perfect field. -/
noncomputable instance instGrpObjReduction : GrpObj (reduction G) where
  one := reductionOne G
  mul := reductionMul G
  one_mul := reductionOneMul G
  mul_one := reductionMulOne G
  mul_assoc := reductionMulAssoc G
  inv := reductionInv G
  left_inv := reductionLeftInv G
  right_inv := reductionRightInv G

/-- The reduction inclusion preserves the unit and multiplication. -/
instance instIsMonHomReductionι : IsMonHom (reductionι G) := sorry

/-- The reduction inclusion, bundled as a morphism of group objects. -/
noncomputable def reductionιGrp :
    Grp.mk (reduction G) ⟶ Grp.mk G :=
  Grp.ofHom (reductionι G)

/-- The raw morphism underlying the bundled reduction inclusion is the reduction inclusion. -/
@[simp]
theorem reductionιGrp_hom_hom :
    (reductionιGrp G).hom.hom = reductionι G := rfl

/-- The underlying scheme morphism of the bundled reduction inclusion is a closed immersion. -/
instance instIsClosedImmersionReductionιGrp :
    IsClosedImmersion ((reductionιGrp G).hom.hom).left := by
  change IsClosedImmersion (Scheme.reductionι G.left)
  simpa using Scheme.isClosedImmersion_reductionι G.left

/-- The reduction of a group scheme over a perfect field as a closed subgroup scheme. -/
noncomputable def reductionClosedSubgroup : Scheme.ClosedSubgroup G :=
  Scheme.ClosedSubgroup.mk ((reductionιGrp G).hom.hom)

end AlgebraicGeometry.Over
