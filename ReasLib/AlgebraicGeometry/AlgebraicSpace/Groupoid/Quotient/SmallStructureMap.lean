/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small

/-!
# Structure morphism of a quotient stack

The canonical `1`-morphism `[U / R] ⟶ 𝒮_B` associated to a groupoid in algebraic
spaces, as a morphism of categories fibred in groupoids over `Over S`.
-/

@[expose] public section

-- Public constructions use private lemmas only in their proof fields.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic space, viewed as a category fibred in groupoids, is a stack on
the big fppf site. -/
instance instIsStackOnSite_toGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    IsStack.OnSite (Scheme.fppfTopology.over S) B.toGroupoids.p :=
  IsStack.InGroupoids.toOnSite inferInstance

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

/-- An arrow of the groupoid prestack preserves the image of its object in the base. -/
private theorem preQuotientToBaseMap_compatible {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total} (f : x ⟶ y) :
    B.functorOfPoints.map f.base.op (G.U.hom.app (op y.base) y.fiber) =
      G.U.hom.app (op x.base) x.fiber := sorry

/-- An arrow of the groupoid prestack maps to the arrow of base-valued points
with its underlying base morphism. -/
private def preQuotientToBaseMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total} (f : x ⟶ y) :
    (op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ : B.toGroupoids.total) ⟶
      op ⟨op y.base, G.U.hom.app (op y.base) y.fiber⟩ :=
  (homMk ⟨op y.base, G.U.hom.app (op y.base) y.fiber⟩
    ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ f.base.op
    (preQuotientToBaseMap_compatible G f)).op

/-- The arrow assignment to base-valued points preserves identities. -/
private theorem preQuotientToBaseMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    preQuotientToBaseMap G (𝟙 x) =
      𝟙 (op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ : B.toGroupoids.total) := sorry

/-- The arrow assignment to base-valued points preserves composition. -/
private theorem preQuotientToBaseMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y z : (preQuotient G).total}
    (f : x ⟶ y) (g : y ⟶ z) :
    preQuotientToBaseMap G (f ≫ g) =
      preQuotientToBaseMap G f ≫ preQuotientToBaseMap G g := sorry

/-- The total functor from the groupoid prestack to the base-space fibration
applies the structure morphism on objects and preserves the underlying base maps. -/
def preQuotientToBaseFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preQuotient G).total ⥤ B.toGroupoids.total where
  obj x := op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩
  map := preQuotientToBaseMap G
  map_id := preQuotientToBaseMap_id G
  map_comp := preQuotientToBaseMap_comp G

/-- On objects, `preQuotientToBaseFunctor` applies the structure morphism `U ⟶ B`. -/
theorem preQuotientToBaseFunctor_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    (preQuotientToBaseFunctor G).obj x =
      op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ := sorry

/-- The functor from the groupoid prestack to the base commutes with projection to schemes. -/
private theorem preQuotientToBaseFunctor_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    preQuotientToBaseFunctor G ⋙ B.toGroupoids.p = (preQuotient G).p := sorry

/-- The canonical `1`-morphism `[U /ₚ R] ⟶ 𝒮_B`. -/
def preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : (preQuotient G) ⟶ B.toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.ofFunctor (preQuotientToBaseFunctor G) (preQuotientToBaseFunctor_over G))

/-- The total functor of `preQuotientToBase` is `preQuotientToBaseFunctor`. -/
theorem preQuotientToBase_toFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toFunctor (preQuotientToBase G) =
      preQuotientToBaseFunctor G := sorry

/-- The selected stackification lift of `preQuotientToBase` through
`[U /ₚ R] ⟶ [U / R]`. -/
def toBaseLift {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (stackificationPresentation G).comparison)
      (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor (preQuotientToBase G)) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (stackificationPresentation G).isStackification
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor (preQuotientToBase G))

/-- The canonical structure morphism `[U / R] ⟶ 𝒮_B` obtained by lifting
`[U /ₚ R] ⟶ 𝒮_B` through stackification. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (quotientStack G) ⟶ B.toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (toBaseLift G).lift.toBasedFunctor

/-- `toBase G` is a based functor over `Over S`. -/
theorem toBase_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toFunctor (toBase G) ⋙ B.toGroupoids.p =
      (quotientStack G).p := sorry

/-- The images of mutually inverse based natural transformations compose to the identity. -/
private theorem ofBasedNatTransIso_hom_inv_id {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {F G : X ⟶ Y}
    (e : FiberedCategoryOver.Groupoids.toBasedFunctor F ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor G) :
    FiberedCategoryOver.Groupoids.ofBasedNatTrans e.hom ≫
      FiberedCategoryOver.Groupoids.ofBasedNatTrans e.inv = 𝟙 F := sorry

/-- The images of inverse based natural transformations compose in reverse order to the identity. -/
private theorem ofBasedNatTransIso_inv_hom_id {S : Scheme.{u}}
    {X Y : GroupoidsOver S} {F G : X ⟶ Y}
    (e : FiberedCategoryOver.Groupoids.toBasedFunctor F ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor G) :
    FiberedCategoryOver.Groupoids.ofBasedNatTrans e.inv ≫
      FiberedCategoryOver.Groupoids.ofBasedNatTrans e.hom = 𝟙 G := sorry

/-- Reconstruct a `2`-isomorphism of groupoid-fibred morphisms from an isomorphism of
underlying based functors. -/
private def ofBasedNatTransIso {S : Scheme.{u}} {X Y : GroupoidsOver S} {F G : X ⟶ Y}
    (e : FiberedCategoryOver.Groupoids.toBasedFunctor F ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor G) : F ≅ G where
  hom := FiberedCategoryOver.Groupoids.ofBasedNatTrans e.hom
  inv := FiberedCategoryOver.Groupoids.ofBasedNatTrans e.inv
  hom_inv_id := ofBasedNatTransIso_hom_inv_id e
  inv_hom_id := ofBasedNatTransIso_inv_hom_id e

/-- The based functor of `stackificationHom ≫ toBase` is the precomposed lift. -/
theorem stackificationHom_comp_toBase_toBasedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toBasedFunctor ((stackificationHom G) ≫ (toBase G)) =
      ((CartesianBasedFunctor.precomp B.toGroupoids.p
          (stackificationPresentation G).comparison).obj
        (toBaseLift G).lift).toBasedFunctor := sorry

/-- The based functor of `preQuotientToBase` is that of its cartesian view. -/
theorem preQuotientToBase_toBasedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (preQuotientToBase G) =
      (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor
        (preQuotientToBase G)).toBasedFunctor := sorry

/-- Precomposing `toBase` with stackification recovers `preQuotientToBase`. -/
def stackificationHom_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackificationHom G) ≫ (toBase G) ≅ preQuotientToBase G :=
  ofBasedNatTransIso
    (eqToIso (stackificationHom_comp_toBase_toBasedFunctor G) ≪≫
      (CartesianBasedFunctor.forget (preQuotient G).p B.toGroupoids.p).mapIso
        (toBaseLift G).comparison ≪≫
      (eqToIso (preQuotientToBase_toBasedFunctor G)).symm)

/-- Associativity alignment for the atlas composite through stackification. -/
private theorem atlas_comp_toBase_assoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlas G) ≫ (toBase G) =
      (atlasToPreQuotient G) ≫ ((stackificationHom G) ≫ (toBase G)) := sorry

/-- Before stackification, the atlas composite is the `1`-morphism associated to `U ⟶ B`. -/
theorem atlasToPreQuotient_comp_preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlasToPreQuotient G) ≫ preQuotientToBase G =
      AlgebraicSpace.toGroupoids.map G.U.hom := sorry

/-- The composite `𝒮_U ⟶ [U / R] ⟶ 𝒮_B` is identified with the `1`-morphism associated
to the structure morphism `U ⟶ B`. -/
def atlas_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlas G) ≫ (toBase G) ≅ AlgebraicSpace.toGroupoids.map G.U.hom :=
  eqToIso (atlas_comp_toBase_assoc G) ≪≫
    whiskerLeftIso (atlasToPreQuotient G) (stackificationHom_comp_toBase G) ≪≫
    eqToIso (atlasToPreQuotient_comp_preQuotientToBase G)

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
