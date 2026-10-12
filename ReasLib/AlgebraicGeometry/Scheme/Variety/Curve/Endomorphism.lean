/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Graph
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.CycleGroup.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Product

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

variable {k : Type u} [Field k]

/-- The graph of a curve endomorphism, transported to the categorical product `C ⨯ C`. -/
def graphCycle {C : SchemeOverField k} [Curve C] (φ : C ⟶ C) :
    AlgebraicCycle (C ⨯ C).left ℤ :=
  AlgebraicCycle.map (Over.prodLeftIsoPullback C C).inv
    (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (AlgebraicCycle.graph φ)

/-- The graph cycle is the pushforward of the graph along the product comparison. -/
theorem graphCycle_def {C : SchemeOverField k} [Curve C] (φ : C ⟶ C) :
    graphCycle φ =
      AlgebraicCycle.map (Over.prodLeftIsoPullback C C).inv
        (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ)) (AlgebraicCycle.graph φ) := sorry

/-- The product of a smooth curve with itself remains smooth over the field. -/
instance instSmooth_prod [IsAlgClosed k] {C : SchemeOverField k}
    [Curve C] [Smooth C.hom] [Projective C.hom] :
    Smooth (C ⨯ C).hom := sorry

/-- The product of a projective curve with itself is proper over the field. -/
instance instIsProper_prod [IsAlgClosed k] {C : SchemeOverField k}
    [Curve C] [Smooth C.hom] [Projective C.hom] :
    IsProper (C ⨯ C).hom := sorry

variable [IsAlgClosed k]
variable {C : SchemeOverField k} [Curve C] [Smooth C.hom] [Projective C.hom]

/-- The product of a smooth curve with itself is regular. -/
instance instRegular_prodLeft : Scheme.Regular (C ⨯ C).left :=
  regular_of_smooth_over_field (C ⨯ C).hom

/-- The diagonal and graph of a non-identity endomorphism intersect properly. -/
theorem graph_intersectProperly_diagonal (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    IntersectProperly (diagonal C) (graphCycle φ) := sorry

/-- The diagonal-graph intersection is supported in dimension zero. -/
theorem intersection_diagonal_graph_mem (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    intersection (diagonal C) (graphCycle φ)
        (graph_intersectProperly_diagonal φ hφ) ∈
      dimensionSubgroup ((C ⨯ C).hom.relativeDimensionFunction (fun _ ↦ 0)) 0 := sorry

/-- The zero-cycle given by the diagonal-graph intersection. -/
def fixedPointCycle (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    CycleGroup (C ⨯ C).left
      ((C ⨯ C).hom.relativeDimensionFunction (fun _ ↦ 0)) 0 :=
  ⟨intersection (diagonal C) (graphCycle φ)
      (graph_intersectProperly_diagonal φ hφ),
    intersection_diagonal_graph_mem φ hφ⟩

/-- Forgetting the support witness of the fixed-point cycle returns the intersection cycle. -/
theorem fixedPointCycle_toAlgebraicCycle (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    CycleGroup.toAlgebraicCycle
        ((C ⨯ C).hom.relativeDimensionFunction (fun _ ↦ 0)) 0
        (fixedPointCycle φ hφ) =
      intersection (diagonal C) (graphCycle φ)
        (graph_intersectProperly_diagonal φ hφ) := sorry

/-- The fixed-point intersection number, computed as the degree of its zero-cycle. -/
def fixedPointNumber (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) : ℤ :=
  CycleGroup.degree (C ⨯ C) (fixedPointCycle φ hφ)

/-- The fixed-point number is the canonical degree of the diagonal-graph cycle. -/
theorem fixedPointNumber_eq_degree (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    fixedPointNumber φ hφ = CycleGroup.degree (C ⨯ C) (fixedPointCycle φ hφ) := sorry

end AlgebraicGeometry.AlgebraicCycle

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k]

/-- The function-field degree of a nonconstant curve endomorphism. -/
def nonconstantEndomorphismDegree {C : SchemeOverField k} [Curve C]
    (φ : C ⟶ C) (hφ : φ.left.IsNonconstant) : ℕ :=
  @Scheme.Hom.inducedFunctionFieldDegree _ _ φ.left inferInstance inferInstance
    (Scheme.Hom.IsNonconstant.isDominant_of_curves hφ)

/-- The degree of a curve endomorphism, with constant maps assigned degree zero. -/
def curveEndomorphismDegree {C : SchemeOverField k} [Curve C] (φ : C ⟶ C) : ℕ :=
  open Classical in
    if h : φ.left.IsNonconstant then nonconstantEndomorphismDegree φ h else 0

/-- A nonconstant curve endomorphism has its induced function-field degree. -/
theorem curveEndomorphismDegree_of_isNonconstant {C : SchemeOverField k}
    [Curve C] (φ : C ⟶ C) (h : φ.left.IsNonconstant) :
    curveEndomorphismDegree φ = nonconstantEndomorphismDegree φ h := sorry

/-- A constant curve endomorphism has degree zero. -/
theorem curveEndomorphismDegree_eq_zero_of_not_isNonconstant
    {C : SchemeOverField k} [Curve C] (φ : C ⟶ C)
    (h : ¬ φ.left.IsNonconstant) :
    curveEndomorphismDegree φ = 0 := sorry

end AlgebraicGeometry.Curve
