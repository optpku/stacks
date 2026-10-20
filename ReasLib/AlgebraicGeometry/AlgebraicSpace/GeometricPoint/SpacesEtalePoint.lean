module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood.Cofiltered
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.PresentationInclusion

/-! # Geometric points of the spaces étale site

The lift-valued site point of a geometric point has the same sheaf fibers as its
restriction to scheme charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

/-- The category of étale neighborhoods of a geometric point of an algebraic space is initially
small in the universe of `etaleLiftFunctor`. -/
instance instInitiallySmall {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    InitiallySmall.{u + 1} (EtaleNeighborhood xbar) :=
  initiallySmall_of_essentiallySmall _

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint.EtaleNeighborhood

namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Covering sieves in the étale topology of algebraic spaces over `X` lift jointly
surjectively through `etaleLiftFunctor xbar`. -/
theorem coversLift_etaleLiftFunctor (xbar : GeometricPoint X) :
    GrothendieckTopology.Point.Fiber.coversLift (spacesEtaleTopology X)
      (etaleLiftFunctor xbar) :=
  sorry

/-- A geometric point of an algebraic space determines a point of the étale site of algebraic
spaces, whose fiber functor sends `U` to the type of lifts of the geometric point through
`U`. -/
noncomputable def toSpacesEtalePoint (xbar : GeometricPoint X) :
    (spacesEtaleTopology X).Point.{u + 1} where
  fiber := etaleLiftFunctor xbar
  jointly_surjective := coversLift_etaleLiftFunctor xbar

/-- The fiber functor of `toSpacesEtalePoint xbar` is `etaleLiftFunctor xbar`. -/
theorem toSpacesEtalePoint_fiber (xbar : GeometricPoint X) :
    (toSpacesEtalePoint xbar).fiber = etaleLiftFunctor xbar :=
  rfl


/-- Restriction from the spaces étale site to scheme charts preserves the fiber at a
geometric point. Both maps send neighborhood sections to their germs. -/
noncomputable def smallEtaleRestrictionStalkIso (xbar : GeometricPoint X)
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) :
    (toSmallEtalePoint xbar).sheafFiber.obj
        ((smallEtalePresentationRestriction X).obj F) ≅
      (toSpacesEtalePoint xbar).sheafFiber.obj F := by
  let R := (smallEtalePresentationRestriction X).obj F
  refine
    { hom := (toSmallEtalePoint xbar).presheafFiberDesc
        (fun U l ↦ (toSpacesEtalePoint xbar).toPresheafFiber
          ((smallEtaleToSpaces X).obj U) (Over.homMk (ofOverMap l.hom) l.fac) F.obj) ?_
      inv := (toSpacesEtalePoint xbar).presheafFiberDesc
        (fun U l ↦ by
          let n : EtaleNeighborhood xbar := Functor.elementsMk (etaleLiftFunctor xbar) U l
          let p := EtaleNeighborhood.geometricPoint n
          let C := SmallEtale.AtlasCharts.atlasObject U.left
          let D : smallEtaleSite X := smallEtaleSite.mk (C.hom ≫ U.hom)
            (@Etale.etale_comp S _ _ C.hom _ U.hom C.prop U.prop)
          let t : OverLift xbar D := OverLift.of (atlasLiftHom p) (by
            change ofOverMap (atlasLiftHom p) ≫ (C.hom ≫ U.hom) = xbar.hom
            rw [← Category.assoc, atlasLiftHom_fac p]
            exact l.w)
          let r : (smallEtaleToSpaces X).obj D ⟶ U :=
            MorphismProperty.Over.homMk C.hom (by rfl)
          exact F.obj.map r.op ≫ (toSmallEtalePoint xbar).toPresheafFiber D t R.obj) ?_
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  all_goals sorry

/-- On a scheme chart, the restriction comparison sends a section's germ to its germ
on the represented algebraic-space chart with the same lift. -/
theorem smallEtaleRestrictionStalkIso_toPresheafFiber (xbar : GeometricPoint X)
    (F : Sheaf (spacesEtaleTopology X) (Type (u + 1))) (U : smallEtaleSite X)
    (l : (toSmallEtalePoint xbar).fiber.obj U) :
    (toSmallEtalePoint xbar).toPresheafFiber U l
        ((smallEtalePresentationRestriction X).obj F).obj ≫
        (smallEtaleRestrictionStalkIso xbar F).hom =
      (toSpacesEtalePoint xbar).toPresheafFiber ((smallEtaleToSpaces X).obj U)
        (Over.homMk (ofOverMap l.hom) l.fac) F.obj :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
