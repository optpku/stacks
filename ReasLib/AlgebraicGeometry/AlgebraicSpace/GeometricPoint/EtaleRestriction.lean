/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AtlasLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationRestriction
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Pointed scheme refinements for étale restriction

Postcomposition preserves geometric-point lifts. Pulling a scheme chart back to a scheme
atlas supplies pointed étale refinements in the domain of an étale morphism of spaces.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {U X : AlgebraicSpace S}

/-- Postcomposition of a pointed étale scheme chart retains its underlying scheme lift. -/
def restrictPostcomposeLift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {V : smallEtaleSite U} (l : OverLift ubar V) :
    OverLift (ubar.map j) ((etaleRestriction j).obj V) :=
  OverLift.of l.hom sorry

/-- The scheme over the base obtained by pulling a chart back to the domain's scheme atlas. -/
def restrictRefinementOver (j : U ⟶ X) (W : smallEtaleSite X) : Over S :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    ((SmallEtale.AtlasCharts.atlasObject U).hom ≫ j)).pullback W.hom

/-- The structural arrow from the represented refinement to the domain space. -/
def restrictRefinementToU (j : U ⟶ X) (W : smallEtaleSite X) :
    ofOver (restrictRefinementOver j W) ⟶ U :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    ((SmallEtale.AtlasCharts.atlasObject U).hom ≫ j)).fst W.hom ≫
      (SmallEtale.AtlasCharts.atlasObject U).hom

/-- The scheme projection from the represented refinement to the original chart. -/
def restrictRefinementToW (j : U ⟶ X) (W : smallEtaleSite X) :
    restrictRefinementOver j W ⟶ W.left :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    ((SmallEtale.AtlasCharts.atlasObject U).hom ≫ j)).snd W.hom

/-- The represented refinement is étale over the domain space. -/
theorem restrictRefinement_etale (j : U ⟶ X) [Etale j] (W : smallEtaleSite X) :
    Etale (restrictRefinementToU j W) :=
  sorry

/-- The represented refinement, regarded as an étale scheme chart of the domain space. -/
def restrictRefinementObj (j : U ⟶ X) [Etale j] (W : smallEtaleSite X) :
    smallEtaleSite U :=
  smallEtaleSite.mk (restrictRefinementToU j W) (restrictRefinement_etale j W)

/-- The atlas lift and a pointed chart lift induce a scheme lift to their represented pullback. -/
def restrictRefinementPoint (j : U ⟶ X) (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    ubar.overObj ⟶ restrictRefinementOver j W :=
  (Functor.relativelyRepresentable.of_diag X.representableDiagonal
    ((SmallEtale.AtlasCharts.atlasObject U).hom ≫ j)).lift
      (yoneda.map (atlasLiftHom ubar)) l.hom sorry

/-- A pointed chart above the image point induces a pointed refinement above the original point. -/
def restrictRefinementLift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    OverLift ubar (restrictRefinementObj j W) :=
  OverLift.of (restrictRefinementPoint j ubar l) sorry

/-- The refinement projection is a morphism of charts after postcomposition. -/
def restrictRefinementHom (j : U ⟶ X) [Etale j] (W : smallEtaleSite X) :
    (etaleRestriction j).obj (restrictRefinementObj j W) ⟶ W :=
  MorphismProperty.CostructuredArrow.homMk (restrictRefinementToW j W) trivial sorry

/-- The postcomposed refinement lift projects to the original pointed chart lift. -/
theorem restrictRefinementHom_lift (j : U ⟶ X) [Etale j] (ubar : GeometricPoint U)
    {W : smallEtaleSite X} (l : OverLift (ubar.map j) W) :
    OverLift.map (restrictRefinementHom j W)
      (restrictPostcomposeLift j ubar (restrictRefinementLift j ubar l)) = l :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
