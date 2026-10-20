/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# The concrete source-target square of the quotient atlas

The source and target maps of a groupoid in algebraic spaces give the
canonical two-cartesian square over its fppf quotient stack.
-/

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck
open CategoryTheory.Bicategory CategoryTheory.Functor
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The two-universe equivalence of the total category of `𝒮_U`. -/
def stackInSetsULiftEquiv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets G.U.left).total ≌
      Cat.twoULift.{u + 1, u, u + 1, u + 1} (stackInSets G.U.left).total :=
  Cat.TwoULift.equiv.{u + 1, u, u + 1, u + 1} (stackInSets G.U.left).total

private theorem sourceTargetPreInvHom_endpoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (spacePointArrow G x ≫ G.i.left) ≫ G.s.left = ((preAtlasTarget G).toFunctor.obj x).fiber ∧
      (spacePointArrow G x ≫ G.i.left) ≫ G.t.left =
        (G.points.map (op (𝟙 ((preAtlasTarget G).toFunctor.obj x).base))).obj
          ((preAtlasSource G).toFunctor.obj x).fiber := sorry

/-- The fibre morphism of `[U/_p R]` associated to the groupoid inverse of an `𝒮_R`-point. -/
def sourceTargetPreInvHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (preAtlasTarget G).toFunctor.obj x ⟶ (preAtlasSource G).toFunctor.obj x where
  base := 𝟙 ((preAtlasTarget G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x ≫ G.i.left)
    (sourceTargetPreInvHom_endpoints G x).1 (sourceTargetPreInvHom_endpoints G x).2

/-- The cartesian source functor `𝒮_R ⟶ 𝒮_U` before lifting to stacks in groupoids. -/
def sourceMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.R.left).p (stackInSetsULift G.U.left).p :=
  ((stackInSetsULift.down G.R.left).comp (stackInSets.map G.s.left)).comp
    (stackInSetsULift.up G.U.left)

/-- The unlifted `𝒮_R`-point underlying a universe-aligned object. -/
def sourceTargetDown {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.R.left).total :=
  (stackInSetsULift.down G.R.left).toFunctor.obj x

/-- The cartesian target functor `𝒮_R ⟶ 𝒮_U` before lifting to stacks in groupoids. -/
def targetMapCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.R.left).p (stackInSetsULift G.U.left).p :=
  ((stackInSetsULift.down G.R.left).comp (stackInSets.map G.t.left)).comp
    (stackInSetsULift.up G.U.left)

/-- The atlas `π : 𝒮_U ⟶ [U/R]` as a morphism of stacks in groupoids, after aligning `𝒮_U`. -/
def atlasULiftHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.U.left ⟶ fppfQuotientStack G :=
  StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor (fppfAtlasULift G).toBasedFunctor)

/-- The source map `s : 𝒮_R ⟶ 𝒮_U` as a morphism of stacks in groupoids. -/
def sourceMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.R.left ⟶ stackInSetsULift G.U.left :=
  stackInSetsULift.map G.s.left

/-- The unlifted source image of a universe-aligned `𝒮_R`-point. -/
def sourceTargetDownSource {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.U.left).total :=
  (stackInSets.map G.s.left).toFunctor.obj (sourceTargetDown G x)

/-- The unlifted target image of a universe-aligned `𝒮_R`-point. -/
def sourceTargetDownTarget {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (stackInSets G.U.left).total :=
  (stackInSets.map G.t.left).toFunctor.obj (sourceTargetDown G x)

/-- The target map `t : 𝒮_R ⟶ 𝒮_U` as a morphism of stacks in groupoids. -/
def targetMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    stackInSetsULift G.R.left ⟶ stackInSetsULift G.U.left :=
  stackInSetsULift.map G.t.left

/-- The component of `α : π ∘ s ⟶ π ∘ t` at a universe-aligned `𝒮_R`-point, after transporting
along the two-universe unit of `𝒮_U`. -/
def sourceTargetIsoHomApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x ⟶
      ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x :=
  (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.inv.app (sourceTargetDownSource G x)) ≫
    (fppfQuotientStackPresentation G).comparison.toFunctor.map
      (sourceTargetPreHom G (sourceTargetDown G x)) ≫
    (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.hom.app (sourceTargetDownTarget G x))

/-- The component of the inverse 2-cell `π ∘ t ⟶ π ∘ s` at a universe-aligned `𝒮_R`-point. -/
def sourceTargetIsoInvApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x ⟶
      ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.obj x :=
  (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.inv.app (sourceTargetDownTarget G x)) ≫
    (fppfQuotientStackPresentation G).comparison.toFunctor.map
      (sourceTargetPreInvHom G (sourceTargetDown G x)) ≫
    (fppfAtlas G).toFunctor.map
      ((stackInSetsULiftEquiv G).unitIso.hom.app (sourceTargetDownSource G x))

private theorem sourceTargetIsoCartesian_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (∀ (x y : (stackInSetsULift G.R.left).total) (f : x ⟶ y),
      ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.map f ≫ sourceTargetIsoHomApp G y =
        sourceTargetIsoHomApp G x ≫ ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.map f) ∧
    (∀ x : (stackInSetsULift G.R.left).total,
      (fppfQuotientStack G).p.IsHomLift (𝟙 ((stackInSetsULift G.R.left).p.obj x))
        (sourceTargetIsoHomApp G x)) ∧
    (∀ (x y : (stackInSetsULift G.R.left).total) (f : x ⟶ y),
      ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor.map f ≫ sourceTargetIsoInvApp G y =
        sourceTargetIsoInvApp G x ≫ ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor.map f) ∧
    (∀ x : (stackInSetsULift G.R.left).total,
      (fppfQuotientStack G).p.IsHomLift (𝟙 ((stackInSetsULift G.R.left).p.obj x))
        (sourceTargetIsoInvApp G x)) := sorry

set_option maxHeartbeats 1000000 in
private def sourceTargetIsoCartesianHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceMapCartesian G).comp (fppfAtlasULift G) ⟶
      (targetMapCartesian G).comp (fppfAtlasULift G) :=
  let η : NatTrans ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor
      ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor :=
    { app := fun x ↦ sourceTargetIsoHomApp G x
      naturality := fun {x y} f ↦ (sourceTargetIsoCartesian_laws G).1 x y f }
  let ηb : BasedNatTrans ((sourceMapCartesian G).comp (fppfAtlasULift G)).toBasedFunctor
      ((targetMapCartesian G).comp (fppfAtlasULift G)).toBasedFunctor :=
    ⟨η, (sourceTargetIsoCartesian_laws G).2.1⟩
  CartesianBasedFunctor.homMk
    (F := (sourceMapCartesian G).comp (fppfAtlasULift G))
    (G := (targetMapCartesian G).comp (fppfAtlasULift G)) ηb

set_option maxHeartbeats 1000000 in
private def sourceTargetIsoCartesianInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (targetMapCartesian G).comp (fppfAtlasULift G) ⟶
      (sourceMapCartesian G).comp (fppfAtlasULift G) :=
  let η : NatTrans ((targetMapCartesian G).comp (fppfAtlasULift G)).toFunctor
      ((sourceMapCartesian G).comp (fppfAtlasULift G)).toFunctor :=
    { app := fun x ↦ sourceTargetIsoInvApp G x
      naturality := fun {x y} f ↦ (sourceTargetIsoCartesian_laws G).2.2.1 x y f }
  let ηb : BasedNatTrans ((targetMapCartesian G).comp (fppfAtlasULift G)).toBasedFunctor
      ((sourceMapCartesian G).comp (fppfAtlasULift G)).toBasedFunctor :=
    ⟨η, (sourceTargetIsoCartesian_laws G).2.2.2⟩
  CartesianBasedFunctor.homMk
    (F := (targetMapCartesian G).comp (fppfAtlasULift G))
    (G := (sourceMapCartesian G).comp (fppfAtlasULift G)) ηb

private theorem sourceTargetIsoCartesian_inverse_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetIsoCartesianHom G ≫ sourceTargetIsoCartesianInv G =
      𝟙 ((sourceMapCartesian G).comp (fppfAtlasULift G))) ∧
    (sourceTargetIsoCartesianInv G ≫ sourceTargetIsoCartesianHom G =
      𝟙 ((targetMapCartesian G).comp (fppfAtlasULift G))) := sorry

/-- The canonical Cartesian isomorphism between the source and target atlas composites. -/
def sourceTargetIsoCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceMapCartesian G).comp (fppfAtlasULift G) ≅
      (targetMapCartesian G).comp (fppfAtlasULift G) where
  hom := sourceTargetIsoCartesianHom G
  inv := sourceTargetIsoCartesianInv G
  hom_inv_id := (sourceTargetIsoCartesian_inverse_laws G).1
  inv_hom_id := (sourceTargetIsoCartesian_inverse_laws G).2

/-- The invertible `2`-cell `α : π ∘ s ≅ π ∘ t` of stacks in groupoids. -/
def sourceTargetIso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    sourceMap G ≫ atlasULiftHom G ≅ targetMap G ≫ atlasULiftHom G :=
  StackOver.Groupoids.Hom.isoMk
    (FiberedCategoryOver.Groupoids.BasedFunctorIso.lift
      (CartesianBasedFunctor.toBasedIso (sourceTargetIsoCartesian G)))

/-- The `2`-commutative square with apex `𝒮_R`, legs `s` and `t`, and bottom atlas `π`. -/
def sourceTargetCone {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    PseudoPullbackCone (atlasULiftHom G) (atlasULiftHom G) where
  pt := stackInSetsULift G.R.left
  fst := sourceMap G
  snd := targetMap G
  iso := sourceTargetIso G

/-- The canonical source-target square of a groupoid in algebraic spaces is a
two-fibre product over its fppf quotient stack. -/
theorem sourceTargetCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).IsBilimit := sorry

/-- `atlasULiftHom` is the morphism-universe inverse of `𝒮_U` followed by `fppfAtlas`. -/
theorem atlasULiftHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids.Hom.toCartesianBasedFunctor (atlasULiftHom G) =
      (stackInSetsULift.down G.U.left).comp (fppfAtlas G) := sorry

/-- The underlying arrow of `sourceTargetPreInvHom` is the groupoid inverse of the scheme-valued
`R`-point. -/
theorem sourceTargetPreInvHom_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreInvHom G x).fiber.arrow = spacePointArrow G x ≫ G.i.left := sorry

/-- A component of `sourceTargetIso.hom` is the stacked image of `sourceTargetPreHom`, transported
along the two-universe unit of `𝒮_U`. -/
theorem sourceTargetIso_hom_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSetsULift G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTargetIsoCartesian G).hom).toNatTrans.app x =
      sourceTargetIsoHomApp G x := sorry

/-- The apex of `sourceTargetCone G` is `𝒮_R`. -/
theorem sourceTargetCone_pt {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).pt = stackInSetsULift G.R.left := sorry

/-- The first projection of `sourceTargetCone G` is `s`. -/
theorem sourceTargetCone_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).fst = sourceMap G := sorry

/-- The second projection of `sourceTargetCone G` is `t`. -/
theorem sourceTargetCone_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).snd = targetMap G := sorry

/-- The `2`-cell of `sourceTargetCone G` is `sourceTargetIso G`. -/
theorem sourceTargetCone_iso {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).iso = sourceTargetIso G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
