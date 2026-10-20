module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Hom
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.Germ

/-!
# Represented field fibres of morphisms to algebraic stacks

An algebraic-space model of a cartesian field fibre carries a canonical
projection to the source and a germ homomorphism on global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory
open AlgebraicGeometry.AlgebraicSpace.GeometricPoint

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The projection `F ⟶ U` of a cartesian field fibre, recovered from an
algebraic-space model of `TwoFibreProduct.apex f p.hom`. -/
def representedFiberι {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    F ⟶ U :=
  AlgebraicSpace.toGroupoids.eval
    (e.inv ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom)

/-- `representedFiberι e` is the morphism of algebraic spaces recovered from
`e.inv ≫ TwoFibreProduct.fst f p.hom`. -/
theorem representedFiberι_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    representedFiberι e =
      AlgebraicSpace.toGroupoids.eval
        (e.inv ≫ TwoFibreProduct.fst.{u + 1, u, u + 1, u} f p.hom) :=
  rfl

/-- The germ `Γ(U, 𝒪_U) →+* 𝒪_{F, zbar}` along `representedFiberι e`, formed in an
étale neighbourhood of the image of `zbar` on `U`. -/
def globalSectionsToRepresentedFiberEtaleLocalRingAt {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X}
    {p : FieldValuedPoint X} {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (zbar : AlgebraicSpace.GeometricPoint F)
    (V : AlgebraicSpace.smallEtaleSite U)
    (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V) :
    AlgebraicSpace.globalSectionsRing U →+* AlgebraicSpace.etaleLocalRing F zbar :=
  ((AlgebraicSpace.etaleLocalRingMap (representedFiberι e) zbar).comp
      (AlgebraicSpace.globalSectionsToEtaleLocalRing U
        (zbar.map (representedFiberι e)))).comp
    (RingCat.Hom.hom
      ((toSmallEtalePoint (zbar.map (representedFiberι e))).toPresheafFiber V l
        (AlgebraicSpace.globalSectionsConstPresheaf U)))

/-- `globalSectionsToRepresentedFiberEtaleLocalRingAt` composes the local ring
map of `representedFiberι e` with the germ of global sections at the image of
`zbar` on `U`. -/
theorem globalSectionsToRepresentedFiberEtaleLocalRingAt_eq {S : Scheme.{u}}
    {U : AlgebraicSpace S} {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X}
    {p : FieldValuedPoint X} {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids)
    (zbar : AlgebraicSpace.GeometricPoint F)
    (V : AlgebraicSpace.smallEtaleSite U)
    (l : (toSmallEtalePoint (zbar.map (representedFiberι e))).fiber.obj V) :
    globalSectionsToRepresentedFiberEtaleLocalRingAt e zbar V l =
      ((AlgebraicSpace.etaleLocalRingMap (representedFiberι e) zbar).comp
          (AlgebraicSpace.globalSectionsToEtaleLocalRing U
            (zbar.map (representedFiberι e)))).comp
        (RingCat.Hom.hom
          ((toSmallEtalePoint (zbar.map (representedFiberι e))).toPresheafFiber V l
            (AlgebraicSpace.globalSectionsConstPresheaf U))) :=
  rfl

/-- The projection `F ⟶ Spec(k)` of a cartesian field fibre, recovered from an
algebraic-space model of `TwoFibreProduct.apex f p.hom`. -/
def representedFiberToSpec {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    F ⟶ AlgebraicSpace.ofOver p.overObj :=
  AlgebraicSpace.toGroupoids.eval
    (e.inv ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom ≫
      (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv)

/-- `representedFiberToSpec e` is the morphism of algebraic spaces recovered from
`e.inv ≫ TwoFibreProduct.snd f p.hom ≫ (ofOverSliceEquiv p.overObj).inv`. -/
theorem representedFiberToSpec_eq {S : Scheme.{u}} {U : AlgebraicSpace S}
    {X : GroupoidsOver S} {f : U.toGroupoids ⟶ X} {p : FieldValuedPoint X}
    {F : AlgebraicSpace S}
    (e : TwoFibreProduct.apex.{u + 1, u, u + 1, u} f p.hom ≌ F.toGroupoids) :
    representedFiberToSpec e =
      AlgebraicSpace.toGroupoids.eval
        (e.inv ≫ TwoFibreProduct.snd.{u + 1, u, u + 1, u} f p.hom ≫
          (AlgebraicSpace.ofOverSliceEquiv p.overObj).inv) :=
  rfl

end AlgebraicGeometry.AlgebraicStack
