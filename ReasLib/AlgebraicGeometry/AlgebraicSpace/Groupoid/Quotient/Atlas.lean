/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Basic

/-!
# The canonical quotient atlas and its groupoid-arrow comparison

The stack of points of the object space maps to the groupoid prestack by sending each point
to the corresponding object and each morphism of points to an identity groupoid arrow.
Composing with the fppf stackification comparison gives the quotient atlas. Points of the
arrow space determine arrows between the source and target composites in the prestack.
A two-universe lift aligns the stack of points with the quotient stack.
-/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions
-- must reference their private endpoint and functor laws under Lean's module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack `[U/_p R]` associated to a groupoid in algebraic spaces, as the co-Grothendieck
projection of the groupoid-valued functor of points. -/
def preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection G.points)

/-- A point of `U` determines an object of its groupoid prestack over the same scheme. -/
private def atlasToPreQuotientObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    (preQuotient G).total where
  base := x.unop.fst.unop
  fiber := yonedaEquiv.symm x.unop.snd

/-- The identity arrow of a point has the endpoints prescribed by restriction along a
morphism in the stack of points. -/
private theorem atlasToPreQuotientMap_endpoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (stackInSets G.U.left).total} (f : x ⟶ y) :
    ((atlasToPreQuotientObj G x).fiber ≫ G.e.left) ≫ G.s.left =
        (atlasToPreQuotientObj G x).fiber ∧
      ((atlasToPreQuotientObj G x).fiber ≫ G.e.left) ≫ G.t.left =
        (G.points.map f.unop.val).obj (atlasToPreQuotientObj G y).fiber := sorry

/-- A morphism of points determines a prestack arrow with the same base map and an identity
groupoid arrow in the fibre. -/
private def atlasToPreQuotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (stackInSets G.U.left).total} (f : x ⟶ y) :
    atlasToPreQuotientObj G x ⟶ atlasToPreQuotientObj G y where
  base := f.unop.val.unop
  fiber :=
    { arrow := yonedaEquiv.symm x.unop.snd ≫ G.e.left
      source := (atlasToPreQuotientMap_endpoints G f).1
      target := (atlasToPreQuotientMap_endpoints G f).2 }

/-- The prestack arrow assigned to the identity of a point is an identity. -/
private theorem atlasToPreQuotientMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    atlasToPreQuotientMap G (𝟙 x) = 𝟙 (atlasToPreQuotientObj G x) := sorry

/-- The assignment of prestack arrows to morphisms of points preserves composition. -/
private theorem atlasToPreQuotientMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y z : (stackInSets G.U.left).total}
    (f : x ⟶ y) (g : y ⟶ z) :
    atlasToPreQuotientMap G (f ≫ g) =
      atlasToPreQuotientMap G f ≫ atlasToPreQuotientMap G g := sorry

/-- The total functor `𝒮_U ⟶ [U/_p R]` sending a functor-of-points value of `U` to the
corresponding object of the co-Grothendieck prestack. Fibre maps are identity arrows of
the discrete fibration `𝒮_U`. -/
def atlasToPreQuotientFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets G.U.left).total ⥤ (preQuotient G).total where
  obj := atlasToPreQuotientObj G
  map := atlasToPreQuotientMap G
  map_id := atlasToPreQuotientMap_id G
  map_comp := atlasToPreQuotientMap_comp G

/-- The point inclusion into the prestack preserves the underlying scheme of each point. -/
theorem atlasToPreQuotientFunctor_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    ((atlasToPreQuotientFunctor G).obj x).base = x.unop.fst.unop := rfl

/-- The fibre of the prestack point inclusion is the scheme-valued point corresponding to
the given functor-of-points value. -/
theorem atlasToPreQuotientFunctor_fiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    ((atlasToPreQuotientFunctor G).obj x).fiber = yonedaEquiv.symm x.unop.snd := rfl

/-- The scheme-valued arrow carried by an object of `𝒮_R`. -/
def spacePointArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    ofOver x.unop.fst.unop ⟶ G.R.left :=
  yonedaEquiv.symm x.unop.snd

/-- The point inclusion into the prestack commutes with projection to schemes. -/
private theorem atlasToPreQuotientFunctor_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    atlasToPreQuotientFunctor G ⋙ (preQuotient G).p = (stackInSets G.U.left).p := sorry

/-- The canonical cartesian `1`-morphism `𝒮_U ⟶ [U/_p R]`. -/
def atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (preQuotient G).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (atlasToPreQuotientFunctor G) (atlasToPreQuotientFunctor_over G))

/-- The canonical cartesian `1`-morphism `𝒮_U ⟶ [U/R]` into the selected fppf quotient stack. -/
def fppfAtlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (fppfQuotientStack G).p :=
  (atlasToPreQuotient G).comp (fppfQuotientStackPresentation G).comparison

/-- The prestack composite `π_p ∘ s : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.s.left).comp (atlasToPreQuotient G)

/-- The prestack composite `π_p ∘ t : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.t.left).comp (atlasToPreQuotient G)

/-- A scheme-valued groupoid arrow has the endpoints obtained from the source and target
maps, with target restricted along the identity base map. -/
private theorem sourceTargetPreHom_endpoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    spacePointArrow G x ≫ G.s.left = ((preAtlasSource G).toFunctor.obj x).fiber ∧
      spacePointArrow G x ≫ G.t.left =
        (G.points.map (op (𝟙 ((preAtlasSource G).toFunctor.obj x).base))).obj
          ((preAtlasTarget G).toFunctor.obj x).fiber := sorry

/-- The fibre isomorphism of `[U/_p R]` associated to an `𝒮_R`-point: the underlying arrow is the
scheme-valued point of `R`, with source `s` and target `t`. -/
def sourceTargetPreHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    (preAtlasSource G).toFunctor.obj x ⟶ (preAtlasTarget G).toFunctor.obj x where
  base := 𝟙 ((preAtlasSource G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x)
    (sourceTargetPreHom_endpoints G x).1 (sourceTargetPreHom_endpoints G x).2

/-- The atlas `𝒮_U ⟶ [U/R]` after aligning `𝒮_U` to the Hom-universe of `[U/R]`. -/
def fppfAtlasULift {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.U.left).p (fppfQuotientStack G).p :=
  (stackInSetsULift.down G.U.left).comp (fppfAtlas G)

end AlgebraicGeometry.GroupoidAlgebraicSpace
