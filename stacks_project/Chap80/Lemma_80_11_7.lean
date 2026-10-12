/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Cartesian.FreeAction
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Definition_78_9_3_Torsor
public import stacks_project.Chap78.Definition_78_19_3_Representable
public import stacks_project.Chap78.Lemma_78_5_2
public import stacks_project.Chap78.Lemma_78_19_4_Representability

/-!
# Free actions of group algebraic spaces

If a group algebraic space `G` over `B` acts freely on an algebraic space `X`
over `B` and `G ⟶ B` is flat and locally of finite presentation, then the fppf
quotient sheaf `X / G` is an algebraic space, a representing morphism
`X ⟶ X / G` is surjective, flat, and locally of finite presentation, and `X`
is an fppf `G`-torsor over `X / G`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj MonoidalLeftAction

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)

/-- A free action of a group algebraic space yields an equivalence relation on the
associated action groupoid. -/
instance instIsEquivalenceRelation_ofAction [Mod.IsFree X] :
    IsEquivalenceRelation (ofAction G X).t (ofAction G X).s := sorry

/-- Flatness of `G ⟶ B` implies flatness of the action-groupoid source
`(g, x) ↦ x`. -/
instance instFlat_ofAction_s [AlgebraicSpace.Flat G.X.hom] :
    AlgebraicSpace.Flat (ofAction G X).s.left := sorry

/-- Flatness of `G ⟶ B` implies flatness of the action-groupoid target
`(g, x) ↦ a(g, x)`, by inversion. -/
instance instFlat_ofAction_t [AlgebraicSpace.Flat G.X.hom] :
    AlgebraicSpace.Flat (ofAction G X).t.left := sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action-groupoid source `(g, x) ↦ x`. -/
instance instLocallyOfFinitePresentation_ofAction_s
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofAction G X).s.left := sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action-groupoid target `(g, x) ↦ a(g, x)`, by inversion. -/
instance instLocallyOfFinitePresentation_ofAction_t
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    AlgebraicSpace.LocallyOfFinitePresentation (ofAction G X).t.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

variable {S : Scheme.{u}} {B : AlgebraicSpace S}
variable (G : GroupAlgebraicSpace B) (X : Action G)

/-- The first projection of `(G ×_B F) ×_F X`, followed by `G ×_B F ⟶ G`,
lands over `B`. -/
theorem restrictToSmulToG_w {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F) :
    ((fst (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left ≫
        AlgebraicSpace.overPullbackFst f G.X) ≫ G.X.hom =
      ((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).hom ≫ f := sorry

/-- The second projection of `(G ×_B F) ×_F X` lands over `B` when `q` is a
morphism over `B`. -/
theorem restrictToSmulToX_w {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom) :
    (snd (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left ≫ X.X.hom =
      ((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).hom ≫ f := sorry

/-- The morphism `(G ×_B F) ×_F X ⟶ G` over `B`. -/
def restrictToSmulHomG {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F) :
    Over.mk (((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).hom ≫ f) ⟶
      G.X :=
  Over.homMk
    ((fst (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left ≫
      AlgebraicSpace.overPullbackFst f G.X)
    (restrictToSmulToG_w G X f q)

/-- The morphism `(G ×_B F) ×_F X ⟶ X` over `B`. -/
def restrictToSmulHomX {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom) :
    Over.mk (((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).hom ≫ f) ⟶
      X.X :=
  Over.homMk
    (snd (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left
    (restrictToSmulToX_w G X f q hq)

/-- The left component of `restrictToSmulHomG` is the composite of the first
projection with `overPullbackFst`. -/
theorem restrictToSmulHomG_left {F : AlgebraicSpace S} (f : F ⟶ B)
    (q : X.X.left ⟶ F) :
    (restrictToSmulHomG G X f q).left =
      (fst (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left ≫
        AlgebraicSpace.overPullbackFst f G.X := sorry

/-- The left component of `restrictToSmulHomX` is the second projection. -/
theorem restrictToSmulHomX_left {F : AlgebraicSpace S} (f : F ⟶ B)
    (q : X.X.left ⟶ F) (hq : q ≫ f = X.X.hom) :
    (restrictToSmulHomX G X f q hq).left =
      (snd (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).left := sorry

/-- The underlying algebraic-space map of the restricted `G_F`-action, obtained by
transporting `γ[G.X, X.X]` along the cartesian comparison
`(G ×_B F) ×_F X ⟶ G ×_B X`. -/
def restrictToSmulLeft {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom) :
    ((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).left ⟶ (Over.mk q).left :=
  (CartesianMonoidalCategory.lift
      (restrictToSmulHomG G X f q) (restrictToSmulHomX G X f q hq)).left ≫
    γ[G.X, X.X].left

/-- `restrictToSmulLeft` equalizes `q` with the structure morphism of
`(G ×_B F) ×_F X` over `F`. -/
theorem restrictToSmulLeft_comp {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    restrictToSmulLeft G X f q hq ≫ q =
      ((AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q).hom := sorry

/-- The restricted action morphism of `G_F` on `X` in `Over F`. -/
def restrictToSmul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (AlgebraicSpace.grpOverPullback G f).X ⊗ Over.mk q ⟶ Over.mk q :=
  Over.homMk (restrictToSmulLeft G X f q hq)
    (restrictToSmulLeft_comp G X f q hq h_eq)

/-- The left component of `restrictToSmul` is `restrictToSmulLeft`. -/
theorem restrictToSmul_left {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictToSmul G X f q hq h_eq).left = restrictToSmulLeft G X f q hq := sorry

/-- The identity-action law for `restrictToSmul`. -/
theorem restrictToSmul_one_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    η[(AlgebraicSpace.grpOverPullback G f).X] ⊵ₗ Over.mk q ≫
        restrictToSmul G X f q hq h_eq =
      (λₗ (Over.mk q)).hom := sorry

/-- The multiplication-action law for `restrictToSmul`. -/
theorem restrictToSmul_mul_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    μ[(AlgebraicSpace.grpOverPullback G f).X] ⊵ₗ Over.mk q ≫
        restrictToSmul G X f q hq h_eq =
      (αₗ (AlgebraicSpace.grpOverPullback G f).X
          (AlgebraicSpace.grpOverPullback G f).X (Over.mk q)).hom ≫
        (AlgebraicSpace.grpOverPullback G f).X ⊴ₗ
            restrictToSmul G X f q hq h_eq ≫
          restrictToSmul G X f q hq h_eq := sorry

/-- The `G_F`-action on `X` over `F` obtained from a `G`-action on `X` over `B`
along a morphism `q : X ⟶ F` over `B`. -/
def restrictTo {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    Action (AlgebraicSpace.grpOverPullback G f) where
  X := Over.mk q
  mod :=
    { smul := restrictToSmul G X f q hq h_eq
      one_smul := restrictToSmul_one_smul G X f q hq h_eq
      mul_smul := restrictToSmul_mul_smul G X f q hq h_eq }

/-- The carrier of `restrictTo` is `X` viewed over `F` via `q`. -/
theorem restrictTo_X {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictTo G X f q hq h_eq).X = Over.mk q := sorry

/-- The stored action morphism of `restrictTo` is `restrictToSmul`. -/
theorem restrictTo_smul {F : AlgebraicSpace S} (f : F ⟶ B) (q : X.X.left ⟶ F)
    (hq : q ≫ f = X.X.hom)
    (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
      (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q) :
    (restrictTo G X f q hq h_eq).mod.smul = restrictToSmul G X f q hq h_eq := sorry

/-- Lemma 80.11.7 (1): let `S` be a scheme. Let `X ⟶ B` be a morphism of algebraic
spaces over `S`. Let `G` be a group algebraic space over `B` acting freely on `X`
over `B`. If `G ⟶ B` is flat and locally of finite presentation, then the fppf
quotient sheaf `X / G` is an algebraic space. -/
@[stacks 06PH]
theorem hasAlgebraicSpaceQuotient_of_isFree [Mod.IsFree X]
    [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    (GroupoidAlgebraicSpace.ofAction G X).HasAlgebraicSpaceQuotient := sorry

section
variable {F : AlgebraicSpace S} (q : X.X.left ⟶ F)
variable (h_eq : (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.t.left ≫ q =
    (GroupoidAlgebraicSpace.ofAction G X).toPreRelation.s.left ≫ q)
variable [Mod.IsFree X] [AlgebraicSpace.Flat G.X.hom]
variable [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom]
variable [IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.quotientSheafDesc q h_eq)]

/-- Lemma 80.11.7 (2): let `S` be a scheme. Let `X ⟶ B` be a morphism of algebraic
spaces over `S`. Let `G` be a group algebraic space over `B` acting freely on `X`
over `B`. If `G ⟶ B` is flat and locally of finite presentation, then a morphism
`q : X ⟶ F` representing `F = X / G` is surjective. -/
@[stacks 06PH, instance]
instance quotientHom_surjective : AlgebraicSpace.Surjective q := sorry

/-- Lemma 80.11.7 (3): let `S` be a scheme. Let `X ⟶ B` be a morphism of algebraic
spaces over `S`. Let `G` be a group algebraic space over `B` acting freely on `X`
over `B`. If `G ⟶ B` is flat and locally of finite presentation, then a morphism
`q : X ⟶ F` representing `F = X / G` is flat. -/
@[stacks 06PH, instance]
instance quotientHom_flat : AlgebraicSpace.Flat q := sorry

/-- Lemma 80.11.7 (4): let `S` be a scheme. Let `X ⟶ B` be a morphism of algebraic
spaces over `S`. Let `G` be a group algebraic space over `B` acting freely on `X`
over `B`. If `G ⟶ B` is flat and locally of finite presentation, then a morphism
`q : X ⟶ F` representing `F = X / G` is locally of finite presentation. -/
@[stacks 06PH, instance]
instance quotientHom_locallyOfFinitePresentation :
    AlgebraicSpace.LocallyOfFinitePresentation q := sorry

/-- The comparison `G ×_B X ⟶ X ×_F X` induced by a representing morphism
`q : X ⟶ F` is an isomorphism. -/
theorem kernelPairLift_isIso :
    IsIso ((GroupoidAlgebraicSpace.ofAction G X).toPreRelation.kernelPairLift q h_eq) :=
  sorry

/-- Lemma 80.11.7 (5): let `S` be a scheme. Let `X ⟶ B` be a morphism of algebraic
spaces over `S`. Let `G` be a group algebraic space over `B` acting freely on `X`
over `B`. If `G ⟶ B` is flat and locally of finite presentation, then `X` is an
fppf `G`-torsor over `X / G`. -/
@[stacks 06PH]
theorem isStandardTorsor_over_quotient (f : F ⟶ B) (hq : q ≫ f = X.X.hom) :
    IsStandardTorsor (AlgebraicSpace.grpOverPullback G f)
      (restrictTo G X f q hq h_eq) StandardTopology.fppf := sorry

end

end AlgebraicGeometry.GroupAlgebraicSpace.Action

