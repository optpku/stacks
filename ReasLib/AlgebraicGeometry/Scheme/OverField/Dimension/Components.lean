/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.RelativeDimensionLocus
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The clopen subscheme of a smooth scheme over a field on which the relative dimension
is `d`, regarded as a scheme over the same field. -/
def dimensionComponent (X : SchemeOverField k) [Smooth X.hom] (d : ℕ) :
    SchemeOverField k :=
  Over.mk ((Scheme.Hom.smoothRelativeDimensionLocus X.hom d).ι ≫ X.hom)

/-- The inclusion of the relative-dimension-`d` component into a smooth scheme. -/
def dimensionComponentι (X : SchemeOverField k) [Smooth X.hom] (d : ℕ) :
    dimensionComponent X d ⟶ X :=
  Over.homMk (Scheme.Hom.smoothRelativeDimensionLocus X.hom d).ι

/-- Each dimension component of a smooth scheme over a field is smooth over that field. -/
instance instSmoothDimensionComponent (X : SchemeOverField k) [Smooth X.hom] (d : ℕ) :
    Smooth (dimensionComponent X d).hom := sorry

/-- The dimension-`d` component has constant relative dimension `d` over the field. -/
instance instRelativeDimensionDimensionComponent (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) : RelativeDimension (dimensionComponent X d).hom d := sorry

/-- The inclusion of a dimension component of a smooth scheme is a closed immersion. -/
instance instIsClosedImmersionDimensionComponentι (X : SchemeOverField k) [Smooth X.hom]
    (d : ℕ) : IsClosedImmersion (dimensionComponentι X d).left := sorry

/-- A quasi-compact scheme locally of finite type over a field has finite Krull dimension. -/
theorem topologicalKrullDim_lt_top (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] : topologicalKrullDim X.left < ⊤ := sorry

end AlgebraicGeometry.SchemeOverField
