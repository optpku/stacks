module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Stalk
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AtlasLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SpacesEtalePoint
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction

/-! # Canonical comparison from pushforward stalks to source stalks -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A lift of the image geometric point through an étale scheme induces a lift of the
original point through its base change. -/
def imageFiberToSpacesBaseChangeFiber {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) {V : smallEtaleSite X}
    (α : (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj V) :
    (GeometricPoint.toSpacesEtalePoint ybar).fiber.obj ((etaleBaseChange f).obj V) :=
  Over.homMk
    (pullback.lift (C := (Over S)ᵒᵖ ⥤ Type u)
      (homFunctor ybar.hom) (homFunctor (ofOverMap α.hom)) α.fac.symm)
    (by
      change pullback.lift (homFunctor ybar.hom) (homFunctor (ofOverMap α.hom))
          α.fac.symm ≫ pullback.fst (homFunctor f) (homFunctor V.hom) = homFunctor ybar.hom
      exact pullback.lift_fst _ _ _)

/-- Evaluation of a pushforward section on a pulled-back atlas chart, followed by its
germ at the original geometric point. -/
def pushforwardStalkSection {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) (U : smallEtaleSite X)
    (α : (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj U) :
    ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G).obj.obj (op U) ⟶
      (etaleAbelianStalk ybar).obj G := by
  let W := (etaleBaseChange f).obj U
  let β := imageFiberToSpacesBaseChangeFiber f ybar α
  let N : GeometricPoint.EtaleNeighborhood ybar :=
    GeometricPoint.EtaleNeighborhood.of W β.left β.w
  let p := N.geometricPoint
  let C := SmallEtale.AtlasCharts.atlasObject W.left
  let D : smallEtaleSite Y := smallEtaleSite.mk (C.hom ≫ W.hom) (@Etale.etale_comp S _ _ C.hom _ W.hom C.prop W.prop)
  let t : (GeometricPoint.toSmallEtalePoint ybar).fiber.obj D :=
    GeometricPoint.OverLift.of (GeometricPoint.atlasLiftHom p) (by
      change ofOverMap (GeometricPoint.atlasLiftHom p) ≫ (C.hom ≫ W.hom) = ybar.hom
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun l ↦ l ≫ W.hom) (GeometricPoint.atlasLiftHom_fac p)).trans β.w))
  let r : (smallEtaleToSpaces Y).obj D ⟶ W :=
    MorphismProperty.Over.homMk C.hom (by rfl)
  exact ((smallEtaleToSpaces Y).op.ranObjObjIsoLimit G.obj (op W)).hom ≫
    limit.π (StructuredArrow.proj (op W) (smallEtaleToSpaces Y).op ⋙ G.obj)
      (StructuredArrow.mk r.op) ≫
    (GeometricPoint.toSmallEtalePoint ybar).toPresheafFiber D t G.obj

/-- Evaluation on pulled-back charts is compatible with restriction of sections and
postcomposition of lifts. -/
theorem pushforwardStalkSection_naturality {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) {U V : smallEtaleSite X}
    (g : U ⟶ V) (α : (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj U) :
    ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G).obj.map g.op ≫
        pushforwardStalkSection f ybar G U α =
      pushforwardStalkSection f ybar G V
        ((GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.map g α) :=
  sorry

/-- The canonical morphism from the pushforward stalk at the image point to the stalk
at the original geometric point, induced by evaluation on pulled-back charts. -/
def pushforwardStalkMap {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (etaleAbelianStalk (ybar.map f)).obj
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G) ⟶
      (etaleAbelianStalk ybar).obj G :=
  (GeometricPoint.toSmallEtalePoint (ybar.map f)).presheafFiberDesc
    (pushforwardStalkSection f ybar G)
    (fun {_ _} g α ↦ pushforwardStalkSection_naturality f ybar G g α)

/-- The canonical pushforward stalk morphism is natural in abelian étale sheaves. -/
theorem pushforwardStalkMap_naturality {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) {G H : EtaleSheaf Y} (φ : G ⟶ H) :
    (etaleAbelianStalk (ybar.map f)).map
        ((sheafPushforward AddCommGrpCat.{u + 1} f).map φ) ≫ pushforwardStalkMap f ybar H =
      pushforwardStalkMap f ybar G ≫ (etaleAbelianStalk ybar).map φ :=
  sorry

/-- A germ maps to the germ of its evaluation on the pulled-back atlas chart. -/
theorem pushforwardStalkMap_toPresheafFiber {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) (U : smallEtaleSite X)
    (α : (GeometricPoint.toSmallEtalePoint (ybar.map f)).fiber.obj U) :
    (GeometricPoint.toSmallEtalePoint (ybar.map f)).toPresheafFiber U α
        ((sheafPushforward AddCommGrpCat.{u + 1} f).obj G).obj ≫
        pushforwardStalkMap f ybar G = pushforwardStalkSection f ybar G U α :=
  (GeometricPoint.toSmallEtalePoint (ybar.map f)).toPresheafFiber_presheafFiberDesc
    (pushforwardStalkSection f ybar G) (fun {_ _} g α ↦ pushforwardStalkSection_naturality f ybar G g α) U α

/-- The natural comparison from pushforward stalks at the image geometric point to
stalks at the original point. -/
def pushforwardStalkNatTrans {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) :
    sheafPushforward AddCommGrpCat.{u + 1} f ⋙ etaleAbelianStalk (ybar.map f) ⟶
      etaleAbelianStalk ybar where
  app G := pushforwardStalkMap f ybar G
  naturality := fun {_ _} φ ↦ pushforwardStalkMap_naturality f ybar φ

/-- The component of the natural stalk comparison is the canonical stalk morphism. -/
theorem pushforwardStalkNatTrans_app {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    (ybar : GeometricPoint Y) (G : EtaleSheaf Y) :
    (pushforwardStalkNatTrans f ybar).app G = pushforwardStalkMap f ybar G :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
