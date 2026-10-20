module

public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.AtlasLift
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.CategoryTheory.Sites.Topos.Sections

/-!
# Geometric stalks of inverse images on algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.GeometricPoint
open AlgebraicGeometry.AlgebraicSpace.Modules
open ModuleCat Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The source atlas pulled back along the target chart, as an actual source scheme chart. -/
def inverseStalkChart {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    smallEtaleSite X :=
  smallEtaleSite.mk
    (ofOverMap
      ((Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)).snd
        (SmallEtale.AtlasCharts.atlasMap X ≫ homFunctor f)) ≫
      (SmallEtale.AtlasCharts.atlasObject X).hom) sorry

/-- The lifted chart maps into the actual base-change algebraic-space object. -/
def inverseStalkChartArrow {X Y : AlgebraicSpace S} (f : X ⟶ Y) (V : smallEtaleSite Y) :
    (smallEtaleToSpaces X).obj (inverseStalkChart f V) ⟶ (etaleBaseChange f).obj V :=
  MorphismProperty.Over.homMk
    (etaleBaseChangeAtlasMap f V :
      ofOver (etaleBaseChangeAtlasScheme f V) ⟶ etaleBaseChangeSpace f V) sorry

/-- Pullback's universal lift combines the given target lift with the actual atlas lift. -/
def inverseStalkChartPoint {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (V : smallEtaleSite Y) (β : OverLift (xbar.map f) V) :
    OverLift xbar (inverseStalkChart f V) := by
  let r := Functor.relativelyRepresentable.of_diag Y.representableDiagonal (homFunctor V.hom)
  exact OverLift.of
    (r.lift (g := SmallEtale.AtlasCharts.atlasMap X ≫ homFunctor f)
      (ofOverMap β.hom) (atlasLift xbar).hom sorry) sorry


/-- Send a scheme-étale lift of `x̄` through `U`, together with a map `U ⟶ X ×_Y V` over `X`,
to the induced lift of `ȳ` through `V`. -/
def xLiftToYLift {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    {V : smallEtaleSite Y} {U : smallEtaleSite X}
    (a : (smallEtaleToSpaces X).obj U ⟶ (etaleBaseChange f).obj V)
    (l : OverLift xbar U) : OverLift (xbar.map f) V :=
  OverLift.of
    (l.hom ≫ Yoneda.fullyFaithful.preimage
      (a.left ≫ etaleBaseChangeSnd f V : yoneda.obj U.left ⟶ yoneda.obj V.left)) sorry

/-- Sections of the skyscraper at `ȳ` over `V`, as a cone under the Kan-extension diagram of
the skyscraper at `x̄` evaluated at `X ×_Y V`. -/
def skyscraperPushforwardCone {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    (E : Type u) (V : (smallEtaleSite Y)ᵒᵖ) :
    Cone
      (StructuredArrow.proj (op ((etaleBaseChange f).obj V.unop))
        (SpacesEtale.AtlasCharts.inclusion X).op ⋙
        ((EtaleTopos.smallEquivalence X).functor.obj
          ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj) where
  pt := ((toSmallEtalePoint (xbar.map f)).skyscraperSheaf E).obj.obj V
  π :=
    { app := fun a ↦
        Pi.lift fun l ↦
          Pi.π (fun _ : (toSmallEtalePoint (xbar.map f)).fiber.obj V.unop ↦ E)
            (xLiftToYLift f xbar a.hom.unop l)
      naturality := fun _ _ _ ↦ sorry }

/-- Component at `V` of the canonical map of skyscraper sheaves `sky_ȳ E ⟶ f_* sky_x̄ E`. -/
def skyscraperPushforwardHom_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (E : Type u) (V : (smallEtaleSite Y)ᵒᵖ) :
    ((toSmallEtalePoint (xbar.map f)).skyscraperSheaf E).obj.obj V ⟶
      ((typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj.obj V :=
  limit.lift _ (skyscraperPushforwardCone f xbar E V) ≫
    ((SpacesEtale.AtlasCharts.inclusion X).op.ranObjObjIsoLimit
        ((EtaleTopos.smallEquivalence X).functor.obj
          ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj
        (op ((etaleBaseChange f).obj V.unop))).inv

/-- Canonical comparison `sky_ȳ E ⟶ f_* sky_x̄ E` of type-valued skyscraper sheaves. -/
def skyscraperPushforwardHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X)
    (E : Type u) :
    (toSmallEtalePoint (xbar.map f)).skyscraperSheaf E ⟶
      (typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E) :=
  InducedCategory.homMk
    { app := fun V ↦ skyscraperPushforwardHom_app f xbar E V
      naturality := fun _ _ _ ↦ sorry }

/-- The comparisons `sky_ȳ ⟶ f_* sky_x̄` are natural in the coefficient type. -/
def skyscraperPushforwardNatTrans {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    (toSmallEtalePoint (xbar.map f)).skyscraperSheafFunctor ⟶
      (toSmallEtalePoint xbar).skyscraperSheafFunctor ⋙ typePushforward f where
  app E := skyscraperPushforwardHom f xbar E
  naturality := fun _ _ _ ↦ sorry

/-- Type-valued inverse-image stalks along `morphismOfTopoi f` map to stalks at `ȳ = f ∘ x̄`. -/
def typeInverseImageStalkHom {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    (morphismOfTopoi f).inverseImage ⋙ (toSmallEtalePoint xbar).sheafFiber ⟶
      (toSmallEtalePoint (xbar.map f)).sheafFiber :=
  (conjugateEquiv
      ((toSmallEtalePoint (xbar.map f)).skyscraperSheafAdjunction (A := Type u))
      ((morphismOfTopoi f).adjunction.comp
        ((toSmallEtalePoint xbar).skyscraperSheafAdjunction (A := Type u)))).symm
    (skyscraperPushforwardNatTrans f xbar)

/-- Reverse skyscraper comparison evaluates on the represented pullback of the actual atlas. -/
def skyscraperPushforwardInv_app {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (E : Type u) (V : (smallEtaleSite Y)ᵒᵖ) :
    ((typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E)).obj.obj V ⟶
      ((toSmallEtalePoint (xbar.map f)).skyscraperSheaf E).obj.obj V :=
  Pi.lift fun β ↦
    EtaleTopos.extensionEvaluation X ((toSmallEtalePoint xbar).skyscraperSheaf E)
      (inverseStalkChartArrow f V.unop) ≫
    Pi.π (fun _ : OverLift xbar (inverseStalkChart f V.unop) ↦ E)
      (inverseStalkChartPoint f xbar V.unop β)

/-- The reverse map from the direct image of the skyscraper at a geometric point to the
skyscraper at its image. -/
def skyscraperPushforwardInv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) (E : Type u) :
    (typePushforward f).obj ((toSmallEtalePoint xbar).skyscraperSheaf E) ⟶
      (toSmallEtalePoint (xbar.map f)).skyscraperSheaf E :=
  InducedCategory.homMk
    { app := fun V ↦ skyscraperPushforwardInv_app f xbar E V
      naturality := sorry }

/-- The reverse skyscraper comparisons are natural in the coefficient type. -/
def skyscraperPushforwardInvNatTrans {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    (toSmallEtalePoint xbar).skyscraperSheafFunctor ⋙ typePushforward f ⟶
      (toSmallEtalePoint (xbar.map f)).skyscraperSheafFunctor where
  app E := skyscraperPushforwardInv f xbar E
  naturality := sorry

/-- Actual reverse stalk map, obtained by mating the geometric skyscraper reverse. -/
def typeInverseImageStalkInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) (xbar : GeometricPoint X) :
    (toSmallEtalePoint (xbar.map f)).sheafFiber ⟶
      (morphismOfTopoi f).inverseImage ⋙ (toSmallEtalePoint xbar).sheafFiber :=
  (conjugateEquiv
      ((morphismOfTopoi f).adjunction.comp
        ((toSmallEtalePoint xbar).skyscraperSheafAdjunction (A := Type u)))
      ((toSmallEtalePoint (xbar.map f)).skyscraperSheafAdjunction (A := Type u))).symm
    (skyscraperPushforwardInvNatTrans f xbar)

/-- Mating the actual reverse skyscraper map recovers the inverse-image stalk. -/
theorem typeInverseImageStalkInv_hom {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    typeInverseImageStalkInv f xbar ≫ typeInverseImageStalkHom f xbar = 𝟙 _ := sorry

/-- The specified geometric reverse also recovers every inverse-image stalk element. -/
theorem typeInverseImageStalkHom_inv {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (xbar : GeometricPoint X) :
    typeInverseImageStalkHom f xbar ≫ typeInverseImageStalkInv f xbar = 𝟙 _ := sorry

end AlgebraicGeometry.AlgebraicSpace
