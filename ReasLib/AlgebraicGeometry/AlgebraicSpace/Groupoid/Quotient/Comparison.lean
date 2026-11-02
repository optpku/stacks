/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas

/-!
# Canonical 2-morphism of the quotient-stack atlas square

This module constructs the canonical vertical 2-morphism `π ∘ s ⟶ π ∘ t` associated to a
groupoid in algebraic spaces. The cell is built first on `[U/_p R]`, sending an `𝒮_R`-point to
the corresponding fibre isomorphism, then transported along stackification.
-/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions must reference their private component and law declarations under Lean’s module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The stacked composite `π ∘ s : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (fppfQuotientStack G).p :=
  (stackInSets.map G.s.left).comp (fppfAtlas G)

/-- The stacked composite `π ∘ t : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (fppfQuotientStack G).p :=
  (stackInSets.map G.t.left).comp (fppfAtlas G)

/-- The stacked component is the image of the scheme-valued groupoid arrow under
stackification. -/
private def sourceTargetHomApp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (atlasSource G).toFunctor.obj x ⟶ (atlasTarget G).toFunctor.obj x :=
  (fppfQuotientStackPresentation G).comparison.toFunctor.map (sourceTargetPreHom G x)

/-- The prestack components are natural and lie over identity morphisms of schemes. -/
private theorem sourceTargetPre_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (∀ (x y : (stackInSets G.R.left).total) (f : x ⟶ y),
      (preAtlasSource G).toFunctor.map f ≫ sourceTargetPreHom G y =
        sourceTargetPreHom G x ≫ (preAtlasTarget G).toFunctor.map f) ∧
    (∀ x : (stackInSets G.R.left).total,
      (preQuotient G).p.IsHomLift (𝟙 ((stackInSets G.R.left).p.obj x))
        (sourceTargetPreHom G x)) := sorry

/-- The stacked components are natural and lie over identity morphisms of schemes. -/
private theorem sourceTarget_laws {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (∀ (x y : (stackInSets G.R.left).total) (f : x ⟶ y),
      (atlasSource G).toFunctor.map f ≫ sourceTargetHomApp G y =
        sourceTargetHomApp G x ≫ (atlasTarget G).toFunctor.map f) ∧
    (∀ x : (stackInSets G.R.left).total,
      (fppfQuotientStack G).p.IsHomLift (𝟙 ((stackInSets G.R.left).p.obj x))
        (sourceTargetHomApp G x)) := sorry

set_option maxHeartbeats 1000000 in
/-- The canonical `2`-morphism `α_p : π_p ∘ s ⟶ π_p ∘ t` of prestacks over `(Sch/S)_fppf`. -/
def sourceTargetPre {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    preAtlasSource G ⟶ preAtlasTarget G :=
  let η : NatTrans (preAtlasSource G).toFunctor (preAtlasTarget G).toFunctor :=
    { app := sourceTargetPreHom G
      naturality := fun {x y} f ↦ (sourceTargetPre_laws G).1 x y f }
  let ηb : BasedNatTrans (preAtlasSource G).toBasedFunctor (preAtlasTarget G).toBasedFunctor :=
    ⟨η, (sourceTargetPre_laws G).2⟩
  CartesianBasedFunctor.homMk (F := preAtlasSource G) (G := preAtlasTarget G) ηb

set_option maxHeartbeats 1000000 in
/-- The canonical `2`-morphism `α : π ∘ s ⟶ π ∘ t` of stacks in groupoids over `(Sch/S)_fppf`,
obtained by applying stackification to the components of `α_p`. -/
def sourceTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    atlasSource G ⟶ atlasTarget G :=
  let η : NatTrans (atlasSource G).toFunctor (atlasTarget G).toFunctor :=
    { app := sourceTargetHomApp G
      naturality := fun {x y} f ↦ (sourceTarget_laws G).1 x y f }
  let ηb : BasedNatTrans (atlasSource G).toBasedFunctor (atlasTarget G).toBasedFunctor :=
    ⟨η, (sourceTarget_laws G).2⟩
  CartesianBasedFunctor.homMk (F := atlasSource G) (G := atlasTarget G) ηb

/-- The fibre arrow of `sourceTargetPreHom` is the scheme-valued `R`-point of `x`. -/
theorem sourceTargetPre_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow = spacePointArrow G x :=
  rfl

/-- The source endpoint of the fibre arrow of `sourceTargetPreHom` is the image under `s`. -/
theorem sourceTargetPre_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow ≫ G.s.left =
      ((preAtlasSource G).toFunctor.obj x).fiber :=
  (sourceTargetPreHom G x).fiber.source

/-- The target endpoint of the fibre arrow of `sourceTargetPreHom` is the image under `t`. -/
theorem sourceTargetPre_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow ≫ G.t.left =
      ((preAtlasTarget G).toFunctor.obj x).fiber := by
  change NatTrans.vcomp (yonedaEquiv.symm x.unop.snd) G.t.left =
    yonedaEquiv.symm (G.t.left.app _ x.unop.snd)
  exact yonedaEquiv_symm_naturality_right _ G.t.left _

/-- A component of the stacked cell is the image of the corresponding prestack component under
stackification. -/
theorem sourceTarget_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTarget G)).toNatTrans.app x =
      (fppfQuotientStackPresentation G).comparison.toFunctor.map (sourceTargetPreHom G x) :=
  rfl

/-- The stacked cell is the image of the prestack cell under the stackification comparison. -/
theorem sourceTarget_whisker {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTarget G)).toNatTrans.app x =
      (fppfQuotientStackPresentation G).comparison.toFunctor.map
        ((CartesianBasedFunctor.toBasedNatTrans (sourceTargetPre G)).toNatTrans.app x) :=
  rfl

end AlgebraicGeometry.GroupoidAlgebraicSpace
