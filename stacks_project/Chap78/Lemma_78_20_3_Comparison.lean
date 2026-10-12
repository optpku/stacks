/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
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



/-- The stacked composite `π ∘ s : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p :=
  (stackInSets.map G.s.left).comp (atlas G)

/-- The stacked composite `π ∘ t : 𝒮_R ⟶ [U/R]`. -/
abbrev atlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (quotientStack G).p :=
  (stackInSets.map G.t.left).comp (atlas G)



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
