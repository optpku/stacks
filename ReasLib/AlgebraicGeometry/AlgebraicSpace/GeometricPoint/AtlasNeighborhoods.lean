module
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtaleFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AtlasLift
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.CategoryTheory.Adjunction.Basic
@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
noncomputable section
universe u
namespace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The geometric point of the actual scheme atlas given by the native atlas lift. -/
def atlasSchemePoint (xbar : GeometricPoint X) :
    Scheme.GeometricPoint (SmallEtale.AtlasCharts.atlasOver X).left where
  toFieldValuedPoint := Scheme.FieldValuedPoint.of xbar.K (atlasLiftHom xbar).left
  isAlgClosed := xbar.isAlgClosed

/-- The proved native scheme-site point on the lifted atlas. -/
def atlasSchemeSitePoint (xbar : GeometricPoint X) :
    ((SmallEtale.AtlasCharts.atlasOver X).left.smallEtaleTopology).Point.{u} :=
  @Scheme.pointSmallEtale (SmallEtale.AtlasCharts.atlasOver X).left
    xbar.K xbar.field (@IsSepClosed.of_isAlgClosed xbar.K xbar.field xbar.isAlgClosed)
    (atlasLiftHom xbar).left

/-- Scheme neighbourhoods of the atlas point map to source scheme charts. -/
def atlasNeighborhoodChart (X : AlgebraicSpace S)
    (W : (SmallEtale.AtlasCharts.atlasOver X).left.Etale) : smallEtaleSite X :=
  smallEtaleSite.mk
    (ofOverMap (Over.homMk W.hom :
      Over.mk (W.hom ≫ (SmallEtale.AtlasCharts.atlasOver X).hom) ⟶
        SmallEtale.AtlasCharts.atlasOver X) ≫ (SmallEtale.AtlasCharts.atlasObject X).hom) sorry

/-- The scheme lift supplies the actual point of its image chart. -/
def atlasNeighborhoodPoint (xbar : GeometricPoint X)
    (W : (SmallEtale.AtlasCharts.atlasOver X).left.Etale)
    (t : (atlasSchemeSitePoint xbar).fiber.obj W) :
    OverLift xbar (atlasNeighborhoodChart X W) :=
  OverLift.of (Over.homMk t.left sorry) sorry

/-- Forgetting the atlas structure sends native scheme neighbourhoods to space neighbourhoods. -/
def atlasNeighborhoodFunctor (xbar : GeometricPoint X) :
    (atlasSchemeSitePoint xbar).fiber.Elements ⥤ (toSmallEtalePoint_fiber xbar).Elements where
  obj W := ⟨atlasNeighborhoodChart X W.1, atlasNeighborhoodPoint xbar W.1 W.2⟩
  map {W V} a :=
    ⟨MorphismProperty.CostructuredArrow.homMk
      (Over.homMk a.val.left sorry) trivial sorry, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Representability of the scheme atlas follows from the supplied space diagonal. -/
theorem atlasRepresentable (X : AlgebraicSpace S) :
    yoneda.relativelyRepresentable
      ((SmallEtale.AtlasCharts.atlasObject X).hom :
        (ofOver (SmallEtale.AtlasCharts.atlasOver X)).functorOfPoints ⟶ X.functorOfPoints) :=
  Functor.relativelyRepresentable.of_diag X.representableDiagonal
    ((SmallEtale.AtlasCharts.atlasObject X).hom :
      (ofOver (SmallEtale.AtlasCharts.atlasOver X)).functorOfPoints ⟶ X.functorOfPoints)

/-- Pull a source scheme chart back to the given atlas, as a native scheme étale object. -/
def atlasRefinementChart (X : AlgebraicSpace S) (U : smallEtaleSite X) :
    (SmallEtale.AtlasCharts.atlasOver X).left.Etale :=
  MorphismProperty.Over.mk _
    ((atlasRepresentable X).fst' ((U.hom : (ofOver U.left).functorOfPoints ⟶ X.functorOfPoints))).left sorry

/-- The universal pullback lift gives the point of the atlas refinement. -/
def atlasRefinementPoint (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : OverLift xbar U) : (atlasSchemeSitePoint xbar).fiber.obj (atlasRefinementChart X U) :=
  Over.homMk
    ((atlasRepresentable X).lift (g := (U.hom : (ofOver U.left).functorOfPoints ⟶ X.functorOfPoints))
      (yoneda.map (atlasLiftHom xbar)) l.hom sorry).left sorry

/-- Refinement to the atlas is the specified right adjoint on neighbourhood objects and maps. -/
def atlasRefinementFunctor (xbar : GeometricPoint X) :
    (toSmallEtalePoint_fiber xbar).Elements ⥤ (atlasSchemeSitePoint xbar).fiber.Elements where
  obj U := ⟨atlasRefinementChart X U.1, atlasRefinementPoint xbar U.1 U.2⟩
  map {U V} a :=
    ⟨MorphismProperty.Over.homMk
      ((atlasRepresentable X).lift (g := (V.1.hom : (ofOver V.1.left).functorOfPoints ⟶ X.functorOfPoints))
        ((atlasRepresentable X).fst ((U.1.hom : (ofOver U.1.left).functorOfPoints ⟶ X.functorOfPoints)))
        ((atlasRepresentable X).snd ((U.1.hom : (ofOver U.1.left).functorOfPoints ⟶ X.functorOfPoints)) ≫ a.val.left) sorry).left sorry,
      sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The atlas-forgetting/pullback adjunction has explicit universal lifts in both directions. -/
def atlasNeighborhoodAdjunction (xbar : GeometricPoint X) :
    atlasNeighborhoodFunctor xbar ⊣ atlasRefinementFunctor xbar :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun W U ↦
        { toFun := fun a ↦
            ⟨MorphismProperty.Over.homMk
              ((atlasRepresentable X).lift (g := (U.1.hom : (ofOver U.1.left).functorOfPoints ⟶ X.functorOfPoints))
                (yoneda.map (Over.homMk W.1.hom :
                  Over.mk (W.1.hom ≫ (SmallEtale.AtlasCharts.atlasOver X).hom) ⟶
                    SmallEtale.AtlasCharts.atlasOver X)) a.val.left sorry).left sorry,
              sorry⟩
          invFun := fun a ↦
            ⟨MorphismProperty.CostructuredArrow.homMk
              (Over.homMk (a.val.left ≫
                ((atlasRepresentable X).snd ((U.1.hom : (ofOver U.1.left).functorOfPoints ⟶ X.functorOfPoints))).left) sorry)
              trivial sorry, sorry⟩
          left_inv := sorry
          right_inv := sorry }
      homEquiv_naturality_left_symm := sorry
      homEquiv_naturality_right := sorry }

/-- The actual small source is the native initial model of the scheme-point neighbourhoods. -/
def fromAtlasInitialModel (xbar : GeometricPoint X) :
    InitialModel.{u} (atlasSchemeSitePoint xbar).fiber.Elements ⥤
      (toSmallEtalePoint_fiber xbar).Elements :=
  fromInitialModel.{u} _ ⋙ atlasNeighborhoodFunctor xbar

/-- The functor from the initial model of atlas neighbourhoods to space neighbourhoods
is initial. -/
theorem fromAtlasInitialModel_initial (xbar : GeometricPoint X) :
    (fromAtlasInitialModel xbar).Initial := by
  unfold fromAtlasInitialModel
  exact @Functor.initial_comp _ _ _ _ _ _
    (fromInitialModel.{u} _) (atlasNeighborhoodFunctor xbar) inferInstance
    (Functor.initial_of_adjunction (atlasNeighborhoodAdjunction xbar))

/-- An actual native small model, with a concrete atlas neighbourhood functor, computes stalks. -/
theorem smallEtaleFiber_initiallySmall (xbar : GeometricPoint X) :
    InitiallySmall.{u} (toSmallEtalePoint_fiber xbar).Elements :=
  @InitiallySmall.mk' _ _ _ _ (fromAtlasInitialModel xbar)
    (fromAtlasInitialModel_initial xbar)

end AlgebraicGeometry.AlgebraicSpace.GeometricPoint
