/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Lemma_67_6_3_UniversallyOpen
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Lemma_78_17_1_Presentation
public import stacks_project.Chap79.Situation_79_9_2_OnField

/-!
# Restriction of a groupoid in algebraic spaces along a field extension

This module records the canonical morphism `Spec(k') ⟶ U` associated to a field
extension `k'/k` when the object space is `Spec(k)`, together with the morphism
properties of the defining restriction diagram.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

section FieldRestriction

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
variable (k' : Type u) [Field k'] [Algebra k k']

/-- The morphism `Spec(k') ⟶ U` of algebraic spaces over `S` induced by a field
extension `k'/k`. -/
def fieldRestrictionMap :
    AlgebraicSpace.ofOver (Over.mk (FieldExtension.specMap k k' ≫ σ)) ⟶ G.U.left :=
  AlgebraicSpace.ofOverHomMk (FieldExtension.specMap k k') rfl ≫
    (IsOnField.objectSpaceIso G σ).inv

/-- The field-restriction map is `ofOverHomMk` of `Spec(k') ⟶ Spec(k)` followed by the
inverse object-space identification. -/
theorem fieldRestrictionMap_eq :
    fieldRestrictionMap G σ k' =
      AlgebraicSpace.ofOverHomMk (FieldExtension.specMap k k') rfl ≫
        (IsOnField.objectSpaceIso G σ).inv :=
  rfl

/-- The object over `B` obtained by extending the field of objects along `k'/k`. -/
def fieldRestrictionOver : Over B :=
  Over.mk (fieldRestrictionMap G σ k' ≫ G.U.hom)

/-- The structure morphism of the field-extension object is `fieldRestrictionMap`
followed by `U ⟶ B`. -/
theorem fieldRestrictionOver_hom :
    (fieldRestrictionOver G σ k').hom = fieldRestrictionMap G σ k' ≫ G.U.hom :=
  rfl

/-- The field-restriction map is a morphism over `B`. -/
theorem fieldRestriction_w :
    fieldRestrictionMap G σ k' ≫ G.U.hom = (fieldRestrictionOver G σ k').hom :=
  rfl

/-- The canonical morphism over `B` from the field-extension object to the original
object space. -/
def fieldRestriction : fieldRestrictionOver G σ k' ⟶ G.U :=
  Over.homMk (fieldRestrictionMap G σ k') (fieldRestriction_w G σ k')

/-- The underlying algebraic-space morphism of `fieldRestriction` is
`fieldRestrictionMap`. -/
theorem fieldRestriction_left :
    (fieldRestriction G σ k').left = fieldRestrictionMap G σ k' :=
  rfl

/-- The field-extension morphism `U' ⟶ U` is affine. -/
instance fieldRestriction_affine :
    AlgebraicSpace.Affine (fieldRestriction G σ k').left :=
  sorry

/-- The restricted groupoid along `k'/k` is on the field `k'`. -/
instance instIsOnField_fieldRestriction :
    IsOnField (G.pullback (fieldRestriction G σ k')) (FieldExtension.specMap k k' ≫ σ) :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
surjective. -/
instance pullbackToSourceSquare_surjective :
    AlgebraicSpace.Surjective (pullbackToSourceSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
flat. -/
instance pullbackToSourceSquare_flat :
    AlgebraicSpace.Flat (pullbackToSourceSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
universally open. -/
instance pullbackToSourceSquare_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullbackToSourceSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
surjective. -/
instance pullbackToTargetSquare_surjective :
    AlgebraicSpace.Surjective (pullbackToTargetSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
flat. -/
instance pullbackToTargetSquare_flat :
    AlgebraicSpace.Flat (pullbackToTargetSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
universally open. -/
instance pullbackToTargetSquare_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullbackToTargetSquare G (fieldRestriction G σ k')).left :=
  sorry

/-- The source map of the restricted groupoid is surjective. -/
instance restrictionSource_surjective :
    AlgebraicSpace.Surjective (G.pullback (fieldRestriction G σ k')).s.left :=
  sorry

/-- The source map of the restricted groupoid is flat. -/
instance restrictionSource_flat :
    AlgebraicSpace.Flat (G.pullback (fieldRestriction G σ k')).s.left :=
  sorry

/-- The source map of the restricted groupoid is universally open. -/
instance restrictionSource_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullback (fieldRestriction G σ k')).s.left :=
  sorry

/-- The target map of the restricted groupoid is surjective. -/
instance restrictionTarget_surjective :
    AlgebraicSpace.Surjective (G.pullback (fieldRestriction G σ k')).t.left :=
  sorry

/-- The target map of the restricted groupoid is flat. -/
instance restrictionTarget_flat :
    AlgebraicSpace.Flat (G.pullback (fieldRestriction G σ k')).t.left :=
  sorry

/-- The target map of the restricted groupoid is universally open. -/
instance restrictionTarget_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullback (fieldRestriction G σ k')).t.left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is surjective. -/
instance sourcePullbackFst_surjective :
    AlgebraicSpace.Surjective (pullback.fst G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is flat. -/
instance sourcePullbackFst_flat :
    AlgebraicSpace.Flat (pullback.fst G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is universally open. -/
instance sourcePullbackFst_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.fst G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is surjective. -/
instance sourcePullbackSnd_surjective :
    AlgebraicSpace.Surjective (pullback.snd G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is flat. -/
instance sourcePullbackSnd_flat :
    AlgebraicSpace.Flat (pullback.snd G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is universally open. -/
instance sourcePullbackSnd_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.snd G.s (fieldRestriction G σ k')).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is surjective. -/
instance targetPullbackFst_surjective :
    AlgebraicSpace.Surjective (pullback.fst (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is flat. -/
instance targetPullbackFst_flat :
    AlgebraicSpace.Flat (pullback.fst (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is universally open. -/
instance targetPullbackFst_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.fst (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is surjective. -/
instance targetPullbackSnd_surjective :
    AlgebraicSpace.Surjective (pullback.snd (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is flat. -/
instance targetPullbackSnd_flat :
    AlgebraicSpace.Flat (pullback.snd (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is universally open. -/
instance targetPullbackSnd_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.snd (fieldRestriction G σ k') G.t).left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is surjective. -/
instance fieldRestriction_surjective :
    AlgebraicSpace.Surjective (fieldRestriction G σ k').left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is flat. -/
instance fieldRestriction_flat :
    AlgebraicSpace.Flat (fieldRestriction G σ k').left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is universally open. -/
instance fieldRestriction_universallyOpen :
    AlgebraicSpace.UniversallyOpen (fieldRestriction G σ k').left :=
  sorry

end FieldRestriction

section FieldBase

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S)

/-- The source map of a groupoid in algebraic spaces on a field is surjective. -/
theorem source_surjective_of_field [IsOnField G σ] : AlgebraicSpace.Surjective G.s.left :=
  sorry

/-- The source map of a groupoid in algebraic spaces on a field is flat. -/
theorem source_flat_of_field [IsOnField G σ] : AlgebraicSpace.Flat G.s.left :=
  sorry

/-- The source map of a groupoid in algebraic spaces on a field is universally open. -/
theorem source_universallyOpen_of_field [IsOnField G σ] :
    AlgebraicSpace.UniversallyOpen G.s.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is surjective. -/
theorem target_surjective_of_field [IsOnField G σ] : AlgebraicSpace.Surjective G.t.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is flat. -/
theorem target_flat_of_field [IsOnField G σ] : AlgebraicSpace.Flat G.t.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is universally open. -/
theorem target_universallyOpen_of_field [IsOnField G σ] :
    AlgebraicSpace.UniversallyOpen G.t.left :=
  sorry

end FieldBase

section FieldRestrictionArrow

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
variable (k' : Type u) [Field k'] [Algebra k k']

/-- The arrow component of the restriction morphism is surjective. -/
instance pullbackHom_arrow_surjective :
    AlgebraicSpace.Surjective (G.pullbackHom (fieldRestriction G σ k')).arrow.left :=
  sorry

/-- The arrow component of the restriction morphism is flat. -/
instance pullbackHom_arrow_flat :
    AlgebraicSpace.Flat (G.pullbackHom (fieldRestriction G σ k')).arrow.left :=
  sorry

/-- The arrow component of the restriction morphism is universally open. -/
instance pullbackHom_arrow_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullbackHom (fieldRestriction G σ k')).arrow.left :=
  sorry

/-- The dotted arrow `R' ⟶ R` is affine. -/
instance pullbackHom_arrow_affine :
    AlgebraicSpace.Affine (G.pullbackHom (fieldRestriction G σ k')).arrow.left :=
  sorry

end FieldRestrictionArrow

end AlgebraicGeometry.GroupoidAlgebraicSpace
