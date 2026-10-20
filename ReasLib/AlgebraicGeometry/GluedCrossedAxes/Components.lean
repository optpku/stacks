/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.GluedCrossedAxes.Gluing
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Gluing

/-!
# Projective-line components of glued crossed axes

The two axes glue through inversion to closed projective-line components.
Their images cover the glued scheme, and their scheme-theoretic intersection
consists of two distinct rational points, corresponding to zero and infinity.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GluedCrossedAxes

/-- Comparison of a standard `ℙ¹` chart with the spectrum of its affine coordinate ring. -/
private def chartToAffineSpec (k : Type u) [Field k] (i : Fin 2) :
    (ProjectiveLine.standardOpens k i).toScheme ⟶
      Spec (.of (MvPolynomial (ULift.{u} (Fin 1)) k)) :=
  (ProjectiveSpace.CoordinateChart.iso (R := k) 1 i).hom ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom

/-- The first component sends the `X`-chart of `ℙ¹` into `Spec(A)` and the `Y`-chart into
`Spec(B)`, along the `x`-axes. -/
private def firstComponentChartMap (k : Type u) [Field k]
    (chart : (ProjectiveLine.standardCover k).I₀) :
    (ProjectiveLine.standardCover k).X chart ⟶ scheme k :=
  chartToAffineSpec k chart.down ≫
    Spec.map (CommRingCat.ofHom (xAxisHom k).toRingHom) ≫
      if chart.down = 0 then chartA k else chartB k

/-- The two `x`-axis chart maps agree on pairwise overlaps. -/
private theorem firstComponentChartMap_compatible (k : Type u) [Field k]
    (i j : (ProjectiveLine.standardCover k).I₀) :
    pullback.fst ((ProjectiveLine.standardCover k).f i)
        ((ProjectiveLine.standardCover k).f j) ≫
      firstComponentChartMap k i =
    pullback.snd ((ProjectiveLine.standardCover k).f i)
        ((ProjectiveLine.standardCover k).f j) ≫
      firstComponentChartMap k j := sorry

/-- The closed immersion of the first `ℙ¹` component, glued from the two `x`-axes. -/
@[no_expose]
def firstComponent (k : Type u) [Field k] :
    ProjectiveLine.scheme k ⟶ scheme k :=
  (ProjectiveLine.standardCover k).glueMorphisms
    (firstComponentChartMap k) (firstComponentChartMap_compatible k)

/-- The first component is a closed immersion. -/
instance firstComponent_isClosedImmersion (k : Type u) [Field k] :
    IsClosedImmersion (firstComponent k) := sorry

/-- The second component sends the `X`-chart of `ℙ¹` into `Spec(A)` and the `Y`-chart into
`Spec(B)`, along the `y`-axes. -/
private def secondComponentChartMap (k : Type u) [Field k]
    (chart : (ProjectiveLine.standardCover k).I₀) :
    (ProjectiveLine.standardCover k).X chart ⟶ scheme k :=
  chartToAffineSpec k chart.down ≫
    Spec.map (CommRingCat.ofHom (yAxisHom k).toRingHom) ≫
      if chart.down = 0 then chartA k else chartB k

/-- The two `y`-axis chart maps agree on pairwise overlaps. -/
private theorem secondComponentChartMap_compatible (k : Type u) [Field k]
    (i j : (ProjectiveLine.standardCover k).I₀) :
    pullback.fst ((ProjectiveLine.standardCover k).f i)
        ((ProjectiveLine.standardCover k).f j) ≫
      secondComponentChartMap k i =
    pullback.snd ((ProjectiveLine.standardCover k).f i)
        ((ProjectiveLine.standardCover k).f j) ≫
      secondComponentChartMap k j := sorry

/-- The closed immersion of the second `ℙ¹` component, glued from the two `y`-axes. -/
@[no_expose]
def secondComponent (k : Type u) [Field k] :
    ProjectiveLine.scheme k ⟶ scheme k :=
  (ProjectiveLine.standardCover k).glueMorphisms
    (secondComponentChartMap k) (secondComponentChartMap_compatible k)

/-- The second component is a closed immersion. -/
instance secondComponent_isClosedImmersion (k : Type u) [Field k] :
    IsClosedImmersion (secondComponent k) := sorry

/-- The first component sends the standard zero section of `ℙ¹` to the first chart origin. -/
theorem firstComponent_comp_zeroSection (k : Type u) [Field k] :
    ProjectiveLine.zeroSection k ≫ firstComponent k = originASection k := sorry

/-- The second component sends the standard zero section of `ℙ¹` to the first chart origin. -/
theorem secondComponent_comp_zeroSection (k : Type u) [Field k] :
    ProjectiveLine.zeroSection k ≫ secondComponent k = originASection k := sorry

/-- The first component sends the standard infinity section of `ℙ¹` to the second chart origin. -/
theorem firstComponent_comp_infinitySection (k : Type u) [Field k] :
    ProjectiveLine.infinitySection k ≫ firstComponent k = originBSection k := sorry

/-- The second component sends the standard infinity section of `ℙ¹` to the second chart origin. -/
theorem secondComponent_comp_infinitySection (k : Type u) [Field k] :
    ProjectiveLine.infinitySection k ≫ secondComponent k = originBSection k := sorry

/-- The first component sends `0 ∈ ℙ¹` to the first chart origin. -/
theorem firstComponent_zeroPoint (k : Type u) [Field k] :
    (firstComponent k).base (ProjectiveLine.zeroPoint k) = originA k := sorry

/-- The first component sends `∞ ∈ ℙ¹` to the second chart origin. -/
theorem firstComponent_infinityPoint (k : Type u) [Field k] :
    (firstComponent k).base (ProjectiveLine.infinityPoint k) = originB k := sorry

/-- The second component sends `0 ∈ ℙ¹` to the first chart origin. -/
theorem secondComponent_zeroPoint (k : Type u) [Field k] :
    (secondComponent k).base (ProjectiveLine.zeroPoint k) = originA k := sorry

/-- The second component sends `∞ ∈ ℙ¹` to the second chart origin. -/
theorem secondComponent_infinityPoint (k : Type u) [Field k] :
    (secondComponent k).base (ProjectiveLine.infinityPoint k) = originB k := sorry

/-- The two zero sections agree after mapping into `X`. -/
private theorem zeroSection_components_compat (k : Type u) [Field k] :
    ProjectiveLine.zeroSection k ≫ firstComponent k =
      ProjectiveLine.zeroSection k ≫ secondComponent k := sorry

/-- The two infinity sections agree after mapping into `X`. -/
private theorem infinitySection_components_compat (k : Type u) [Field k] :
    ProjectiveLine.infinitySection k ≫ firstComponent k =
      ProjectiveLine.infinitySection k ≫ secondComponent k := sorry

/-- The two `k`-points at which the components meet, as a morphism from `Spec k ⨿ Spec k`. -/
@[no_expose]
def componentsIntersection (k : Type u) [Field k] :
    Spec (.of k) ⨿ Spec (.of k) ⟶
      pullback (firstComponent k) (secondComponent k) :=
  coprod.desc
    (pullback.lift (ProjectiveLine.zeroSection k) (ProjectiveLine.zeroSection k)
      (zeroSection_components_compat k))
    (pullback.lift (ProjectiveLine.infinitySection k) (ProjectiveLine.infinitySection k)
      (infinitySection_components_compat k))

/-- The two components meet exactly at two `k`-points. -/
instance componentsIntersection_isIso (k : Type u) [Field k] :
    IsIso (componentsIntersection k) := sorry

/-- The scheme-theoretic intersection of the two `ℙ¹` components is two copies of `Spec k`. -/
def componentsPullbackIso (k : Type u) [Field k] :
    pullback (firstComponent k) (secondComponent k) ≅
      Spec (.of k) ⨿ Spec (.of k) :=
  (asIso (componentsIntersection k)).symm

/-- `componentsPullbackIso` is inverse to the two-point intersection morphism. -/
theorem componentsPullbackIso_hom (k : Type u) [Field k] :
    (componentsPullbackIso k).hom = inv (componentsIntersection k) := sorry

/-- geometrically, `X` is the union of two copies of `ℙ¹_k`. -/
theorem isUnionOfTwoProjectiveLines (k : Type u) [Field k] :
    Function.Surjective (coprod.desc (firstComponent k) (secondComponent k)).base := sorry

end AlgebraicGeometry.GluedCrossedAxes
