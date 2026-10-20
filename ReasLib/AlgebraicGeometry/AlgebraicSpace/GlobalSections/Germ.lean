module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.ToSpec
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FieldFiber

/-! # Germs of global functions on algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Restriction of `Γ(X, 𝒪_X)` to the value of the structure sheaf on an object of
the small étale site, obtained from the canonical map `X ⟶ Spec Γ(X, 𝒪_X)`. -/
def globalSectionsRestrict {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    globalSectionsRing X ⟶ Γ((smallEtaleToScheme X).obj U, ⊤) :=
  (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
    ((Yoneda.fullyFaithful.preimage (U.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop

/-- The restriction of global functions as a morphism of underlying rings on the
small étale site. -/
def globalSectionsToStructureSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (structureSheaf X).obj.obj (op U) :=
  (forget₂ CommRingCat RingCat).map (globalSectionsRestrict U)

/-- The constant ring presheaf with value `Γ(X, 𝒪_X)`. -/
def globalSectionsConstPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const (smallEtaleSite X)ᵒᵖ).obj
    ((forget₂ CommRingCat RingCat).obj (globalSectionsRing X))

/-- Restriction of global functions as a morphism of ring presheaves on the small
étale site. -/
def globalSectionsToStructureSheafHom {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsConstPresheaf X ⟶ (structureSheaf X).obj where
  app U := globalSectionsToStructureSheaf U.unop
  naturality := fun _ _ _ ↦ sorry

/-- Components of `globalSectionsToStructureSheafHom` are `globalSectionsToStructureSheaf`. -/
theorem globalSectionsToStructureSheafHom_app {S : Scheme.{u}} (X : AlgebraicSpace S)
    (U : (smallEtaleSite X)ᵒᵖ) :
    (globalSectionsToStructureSheafHom X).app U =
      globalSectionsToStructureSheaf U.unop :=
  rfl

/-- The germ map on stalks induced by `globalSectionsToStructureSheafHom`. -/
private def globalSectionsToEtaleLocalRingCat {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) :
    ((toSmallEtalePoint xbar).presheafFiber (A := RingCat.{u})).obj (globalSectionsConstPresheaf X) ⟶
      ((toSmallEtalePoint xbar).presheafFiber (A := RingCat.{u})).obj (structureSheaf X).obj :=
  ((toSmallEtalePoint xbar).presheafFiber (A := RingCat.{u})).map (globalSectionsToStructureSheafHom X)

/-- The germ map sending the stalk of the constant global-sections presheaf to the
étale local ring at a geometric point. -/
@[no_expose] def globalSectionsToEtaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) :
    ((toSmallEtalePoint xbar).presheafFiber (A := RingCat.{u})).obj (globalSectionsConstPresheaf X) →+*
      etaleLocalRing X xbar :=
  RingCat.Hom.hom (globalSectionsToEtaleLocalRingCat X xbar)

/-- For every lift of `xbar` through an étale neighbourhood, the germ of a global
section is the image of its restriction under the stalk coprojection. -/
theorem globalSectionsToEtaleLocalRing_spec {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) (U : smallEtaleSite X)
    (l : (toSmallEtalePoint xbar).fiber.obj U) (a : globalSectionsRing X) :
    globalSectionsToEtaleLocalRing X xbar
        (RingCat.Hom.hom
          ((toSmallEtalePoint xbar).toPresheafFiber U l
            (globalSectionsConstPresheaf X)) a) =
      RingCat.Hom.hom
        ((toSmallEtalePoint xbar).toPresheafFiber U l (structureSheaf X).obj)
        (globalSectionsToStructureSheaf U a) :=
  sorry

/-- The composite germ along the field-valued fibre of `f` at `p`. -/
def globalSectionsToFiberEtaleLocalRing {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) (zbar : GeometricPoint (fieldFiber f p)) :
    ((toSmallEtalePoint (zbar.map (fieldFiberι f p))).presheafFiber (A := RingCat.{u})).obj
        (globalSectionsConstPresheaf X) →+*
      etaleLocalRing (fieldFiber f p) zbar :=
  (etaleLocalRingMap (fieldFiberι f p) zbar).comp
    (globalSectionsToEtaleLocalRing X (zbar.map (fieldFiberι f p)))

/-- The germ `Γ(X, 𝒪_X) →+* 𝒪_{F, zbar}` formed in an étale neighbourhood of the
image of `zbar` on `X`. -/
def globalSectionsToFiberEtaleLocalRingAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (p : FieldValuedPoint Y) (zbar : GeometricPoint (fieldFiber f p))
    (U : smallEtaleSite X)
    (l : (toSmallEtalePoint (zbar.map (fieldFiberι f p))).fiber.obj U) :
    globalSectionsRing X →+* etaleLocalRing (fieldFiber f p) zbar :=
  (globalSectionsToFiberEtaleLocalRing f p zbar).comp
    (RingCat.Hom.hom
      ((toSmallEtalePoint (zbar.map (fieldFiberι f p))).toPresheafFiber U l
        (globalSectionsConstPresheaf X)))

end AlgebraicGeometry.AlgebraicSpace
