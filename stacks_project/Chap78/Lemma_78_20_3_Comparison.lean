module

public import stacks_project.Chap78.Lemma_78_20_2_Atlas

/-!
# Canonical 2-morphism of the quotient-stack atlas square

This module constructs the canonical vertical 2-morphism `π ∘ s ⟶ π ∘ t` associated to a
groupoid in algebraic spaces. The cell is built first on `[U/_p R]`, sending an `𝒮_R`-point to
the corresponding fibre isomorphism, then transported along stackification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack composite `π_p ∘ s : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.s.left).comp (atlasToPreQuotient G)

/-- The prestack composite `π_p ∘ t : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.t.left).comp (atlasToPreQuotient G)

/-- The stacked composite `π ∘ s : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p :=
  (stackInSets.map G.s.left).comp (atlas G)

/-- The stacked composite `π ∘ t : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p :=
  (stackInSets.map G.t.left).comp (atlas G)

/-- The scheme-valued arrow carried by an object of `𝒮_R`. -/
def spacePointArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    ofOver x.unop.fst.unop ⟶ G.R.left :=
  yonedaEquiv.symm x.unop.snd

/-- The fibre isomorphism of `[U/_p R]` associated to an `𝒮_R`-point: the underlying arrow is the
scheme-valued point of `R`, with source `s` and target `t`. -/
def sourceTargetPreHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    (preAtlasSource G).toFunctor.obj x ⟶ (preAtlasTarget G).toFunctor.obj x where
  base := 𝟙 ((preAtlasSource G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x) sorry sorry

/-- The canonical `2`-morphism `α_p : π_p ∘ s ⟶ π_p ∘ t` of prestacks over `(Sch/S)_fppf`. -/
def sourceTargetPre {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    preAtlasSource G ⟶ preAtlasTarget G :=
  CartesianBasedFunctor.homMk
    { app := fun x ↦ sourceTargetPreHom G x
      naturality := sorry
      isHomLift' := sorry }

/-- The canonical `2`-morphism `α : π ∘ s ⟶ π ∘ t` of stacks in groupoids over `(Sch/S)_fppf`,
obtained by applying stackification to the components of `α_p`. -/
def sourceTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    atlasSource G ⟶ atlasTarget G :=
  CartesianBasedFunctor.homMk
    { app := fun x ↦
        (stackificationPresentation G).comparison.toFunctor.map (sourceTargetPreHom G x)
      naturality := sorry
      isHomLift' := sorry }

/-- The fibre arrow of `sourceTargetPreHom` is the scheme-valued `R`-point of `x`. -/
theorem sourceTargetPre_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow = spacePointArrow G x :=
  sorry

/-- The source endpoint of the fibre arrow of `sourceTargetPreHom` is the image under `s`. -/
theorem sourceTargetPre_source {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow ≫ G.s.left =
      ((preAtlasSource G).toFunctor.obj x).fiber :=
  sorry

/-- The target endpoint of the fibre arrow of `sourceTargetPreHom` is the image under `t`. -/
theorem sourceTargetPre_target {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (sourceTargetPreHom G x).fiber.arrow ≫ G.t.left =
      ((preAtlasTarget G).toFunctor.obj x).fiber :=
  sorry

/-- A component of the stacked cell is the image of the corresponding prestack component under
stackification. -/
theorem sourceTarget_app {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTarget G)).toNatTrans.app x =
      (stackificationPresentation G).comparison.toFunctor.map (sourceTargetPreHom G x) :=
  sorry

/-- The stacked cell is the image of the prestack cell under the stackification comparison. -/
theorem sourceTarget_whisker {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (CartesianBasedFunctor.toBasedNatTrans (sourceTarget G)).toNatTrans.app x =
      (stackificationPresentation G).comparison.toFunctor.map
        ((CartesianBasedFunctor.toBasedNatTrans (sourceTargetPre G)).toNatTrans.app x) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
