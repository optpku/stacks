/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

/-!
# The concrete source-target square of the quotient atlas

The constructions retain their original public names and concrete data.
Existing proposition-valued laws remain explicit proof obligations.
-/

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

/-- The fibre morphism of `[U/_p R]` associated to the groupoid inverse of an `𝒮_R`-point. -/
def sourceTargetPreInvHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.R.left).total) :
    (preAtlasTarget G).toFunctor.obj x ⟶ (preAtlasSource G).toFunctor.obj x where
  base := 𝟙 ((preAtlasTarget G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x ≫ G.i.left) sorry sorry

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

/-- The cartesian `2`-isomorphism `π ∘ s ≅ π ∘ t` after aligning Hom-universes. -/
def sourceTargetIsoCartesian {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceMapCartesian G).comp (fppfAtlasULift G) ≅
      (targetMapCartesian G).comp (fppfAtlasULift G) where
  hom :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ sourceTargetIsoHomApp G x
        naturality := sorry
        isHomLift' := sorry }
  inv :=
    CartesianBasedFunctor.homMk
      { app := fun x ↦ sourceTargetIsoInvApp G x
        naturality := sorry
        isHomLift' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

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

/-- Lemma 78.22.2: Assume `B → S`, `(U, R, s, t, c)`, and `π : 𝒮_U ⟶ [U/R]` are as in
Lemma 78.20.2. The 2-commutative square of Lemma 78.20.3 with apex `𝒮_R`, legs `s` and `t`,
and comparison `α : π ∘ s ⟶ π ∘ t` is a 2-fibre product of stacks in groupoids on
`(Sch/S)_fppf`. -/
@[instance]
instance sourceTargetCone_isBilimit {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (sourceTargetCone G).IsBilimit := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
