/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.InseparableCubic

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Example 53.13.6 (1): the explicit nonsingular projective cubic has genus one. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.genus_eq_one :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    @SchemeOverField.genus k _ (InseparableCubic.schemeOver a) (InseparableCubic.instProper a)
      (topologicalKrullDim_eq_one (InseparableCubic.schemeOver a)) (InseparableCubic.globalSectionsMap_bijective a) = 1)

/- Example 53.13.6 (2): the standard projective line has genus zero. -/
@[stacks 0CD1] #check (AlgebraicGeometry.ProjectiveSpace.line_genus_eq_zero :
  ∀ (k : Type u) [Field k],
    @SchemeOverField.genus k _ (ProjectiveSpace.schemeOver k 1) (ProjectiveSpace.toSpec_isProper k 1)
      (topologicalKrullDim_eq_one (ProjectiveSpace.schemeOver k 1)) (ProjectiveSpace.line_globalSectionsMap_bijective k) = 0)

/- Example 53.13.6 (3): the constructed projection induces a degree-three extension. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.xProjection_degree_eq_three :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    (InseparableCubic.xProjection a).inducedFunctionFieldDegree = 3)

/- Example 53.13.6 (4): the induced function-field extension is purely inseparable. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.xProjection_isPurelyInseparable :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    ((InseparableCubic.xProjection a).functionFieldMap
      (InseparableCubic.xProjection a).map_genericPoint_eq_of_isDominant).IsPurelyInseparable)

/- Example 53.13.6 (5): the constructed cubic is an integral curve over the field. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instCurve :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    Curve (InseparableCubic.schemeOver a))

/- Example 53.13.6 (6): the cubic is nonsingular in the sense of regularity. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instRegular :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    Scheme.Regular (InseparableCubic.scheme a))

/- Example 53.13.6 (7): the constructed closed immersion exhibits projectivity. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instClosedImmersion :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    IsClosedImmersion (InseparableCubic.iota a))

/- Example 53.13.6 (8): the cubic is proper over the field. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instProper :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    IsProper (InseparableCubic.toSpec a))

/- Example 53.13.6 (9): the chart containing `(0 : 1 : 0)` is smooth over the field. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instSmoothInfinityChart :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    Smooth ((InseparableCubic.chart a 1).ι ≫ InseparableCubic.toSpec a))

/- Example 53.13.6 (10): the zeroth affine chart has equation `x² - y³ + a`. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.equation_dehomogenizeAt_zero :
  ∀ {k : Type u} [Field k] (a : k),
    ProjectiveSpace.dehomogenizeAt 2 0 (Equiv.refl (Fin 2)) (InseparableCubic.equation a) =
      MvPolynomial.X (0 : Fin 2) ^ 2 - MvPolynomial.X (1 : Fin 2) ^ 3 + MvPolynomial.C a)

/- Example 53.13.6 (11): the projection is a morphism over the coefficient field. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.xProjection_toSpec :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    InseparableCubic.xProjection a ≫ ProjectiveSpace.toSpec k 1 = InseparableCubic.toSpec a)

/- Example 53.13.6 (12): the projection's affine domain is the zeroth cubic chart. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.xProjection_preimage_chart :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    InseparableCubic.xProjection a ⁻¹ᵁ
      (ProjectiveSpace.coordinateBasicOpen (R := k) 1 0 : (ProjectiveSpace.scheme k 1).Opens) =
      InseparableCubic.chart a 0)

/- Example 53.13.6 (13): the projection on the affine chart sends `(x, y)` to `x`. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.xProjection_coordinate :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    ((InseparableCubic.xProjection a).appLE
      (ProjectiveSpace.coordinateBasicOpen (R := k) 1 0 : (ProjectiveSpace.scheme k 1).Opens)
      (InseparableCubic.chart a 0) (InseparableCubic.xProjection_preimage_chart a).ge).hom
        ((ProjectiveSpace.coordinateBasicOpenIsoAway (R := k) 1 0).hom
          (ProjectiveSpace.coordinateRatio (R := k) 1 0 (Equiv.refl (Fin 1)) 0)) =
      InseparableCubic.chartCoordinate a 0)

/- Example 53.13.6 (14): the projection is dominant. -/
@[stacks 0CD1] #check (AlgebraicGeometry.InseparableCubic.instDominant :
  ∀ {k : Type u} [Field k] [CharP k 3] (a : k)
    [Fact (a ∉ Set.range (fun element : k ↦ element ^ 3))],
    IsDominant (InseparableCubic.xProjection a))
