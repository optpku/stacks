/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_5_Comparison
public import stacks_project.Chap68.Lemma_68_18_6_Fibre
public import stacks_project.Chap69.Lemma_69_16_2_ToSpec
public import stacks_project.Chap69.Situation_69_16_1_GlobalSections

/-!
# Germs of global functions on algebraic spaces

A global section of `𝒪_X` restricts to every object of the small étale site, and
therefore determines an element of the étale local ring at any geometric point.
-/

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
    ((toOverHom (U.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop

/-- `globalSectionsRestrict U` is the `ΓSpec` adjunct of the composite of `U` with
`toSpecGamma X`. -/
theorem globalSectionsRestrict_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    globalSectionsRestrict U =
      (Scheme.ΓSpecIso (globalSectionsRing X)).inv ≫
        ((toOverHom (U.hom ≫ toSpecGamma X)).left ≫ specGamma_fst X).appTop :=
  sorry

/-- The restriction of global functions as a morphism of underlying rings on the
small étale site. -/
def globalSectionsToStructureSheaf {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    (forget₂ CommRingCat RingCat).obj (globalSectionsRing X) ⟶
      (structureSheaf X).obj.obj (op U) :=
  (forget₂ CommRingCat RingCat).map (globalSectionsRestrict U)

/-- `globalSectionsToStructureSheaf U` is `forget₂` of `globalSectionsRestrict U`. -/
theorem globalSectionsToStructureSheaf_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallEtaleSite X) :
    globalSectionsToStructureSheaf U =
      (forget₂ CommRingCat RingCat).map (globalSectionsRestrict U) :=
  sorry

/-- The constant ring presheaf with value `Γ(X, 𝒪_X)`. -/
def globalSectionsConstPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u} :=
  (Functor.const (smallEtaleSite X)ᵒᵖ).obj
    ((forget₂ CommRingCat RingCat).obj (globalSectionsRing X))

/-- `globalSectionsConstPresheaf X` is the constant functor on the underlying ring of
`Γ(X, 𝒪_X)`. -/
theorem globalSectionsConstPresheaf_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    globalSectionsConstPresheaf X =
      (Functor.const (smallEtaleSite X)ᵒᵖ).obj
        ((forget₂ CommRingCat RingCat).obj (globalSectionsRing X)) :=
  sorry

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
  sorry

/-- The ring-valued fibre functor of the small étale site at a geometric point. -/
abbrev etalePresheafFiberRing {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    ((smallEtaleSite X)ᵒᵖ ⥤ RingCat.{u}) ⥤ RingCat.{u} :=
  (toSmallEtalePoint xbar).presheafFiber

/-- `etalePresheafFiberRing xbar` is the ring-valued `presheafFiber` of
`toSmallEtalePoint xbar`. -/
theorem etalePresheafFiberRing_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (xbar : GeometricPoint X) :
    etalePresheafFiberRing xbar = (toSmallEtalePoint xbar).presheafFiber :=
  sorry

/-- The germ map on stalks induced by `globalSectionsToStructureSheafHom`. -/
def globalSectionsToEtaleLocalRingCat {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) :
    (etalePresheafFiberRing xbar).obj (globalSectionsConstPresheaf X) ⟶
      (etalePresheafFiberRing xbar).obj (structureSheaf X).obj :=
  (etalePresheafFiberRing xbar).map (globalSectionsToStructureSheafHom X)

/-- `globalSectionsToEtaleLocalRingCat` is the fibre of
`globalSectionsToStructureSheafHom`. -/
theorem globalSectionsToEtaleLocalRingCat_eq {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) :
    globalSectionsToEtaleLocalRingCat X xbar =
      (etalePresheafFiberRing xbar).map (globalSectionsToStructureSheafHom X) :=
  sorry

/-- The germ map sending the stalk of the constant global-sections presheaf to the
étale local ring at a geometric point. -/
def globalSectionsToEtaleLocalRing {S : Scheme.{u}} (X : AlgebraicSpace S)
    (xbar : GeometricPoint X) :
    (etalePresheafFiberRing xbar).obj (globalSectionsConstPresheaf X) →+*
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
    (etalePresheafFiberRing (zbar.map (fieldFiberι f p))).obj
        (globalSectionsConstPresheaf X) →+*
      etaleLocalRing (fieldFiber f p) zbar :=
  (etaleLocalRingMap (fieldFiberι f p) zbar).comp
    (globalSectionsToEtaleLocalRing X (zbar.map (fieldFiberι f p)))

/-- `globalSectionsToFiberEtaleLocalRing` is the local ring map of the fibre inclusion
composed with the germ map on `X`. -/
theorem globalSectionsToFiberEtaleLocalRing_eq {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y)
    (zbar : GeometricPoint (fieldFiber f p)) :
    globalSectionsToFiberEtaleLocalRing f p zbar =
      (etaleLocalRingMap (fieldFiberι f p) zbar).comp
        (globalSectionsToEtaleLocalRing X (zbar.map (fieldFiberι f p))) :=
  sorry

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

/-- `globalSectionsToFiberEtaleLocalRingAt` composes the fibre germ with the
coprojection of the constant global-sections presheaf at the given lift. -/
theorem globalSectionsToFiberEtaleLocalRingAt_eq {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (p : FieldValuedPoint Y)
    (zbar : GeometricPoint (fieldFiber f p)) (U : smallEtaleSite X)
    (l : (toSmallEtalePoint (zbar.map (fieldFiberι f p))).fiber.obj U) :
    globalSectionsToFiberEtaleLocalRingAt f p zbar U l =
      (globalSectionsToFiberEtaleLocalRing f p zbar).comp
        (RingCat.Hom.hom
          ((toSmallEtalePoint (zbar.map (fieldFiberι f p))).toPresheafFiber U l
            (globalSectionsConstPresheaf X))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
