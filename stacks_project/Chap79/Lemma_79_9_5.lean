module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Field
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.OnField

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

section FieldRestriction

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
variable (k' : Type u) [Field k'] [Algebra k k']

/- Lemma 79.9.5 (1): the canonical map from the restricted arrows to the source pullback
square is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToSourceSquare_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullbackToSourceSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (2): the canonical map from the restricted arrows to the source pullback
square is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToSourceSquare_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullbackToSourceSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (3): the canonical map from the restricted arrows to the source pullback
square is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToSourceSquare_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullbackToSourceSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (4): the canonical map from the restricted arrows to the target pullback
square is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToTargetSquare_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullbackToTargetSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (5): the canonical map from the restricted arrows to the target pullback
square is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToTargetSquare_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullbackToTargetSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (6): the canonical map from the restricted arrows to the target pullback
square is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackToTargetSquare_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullbackToTargetSquare G
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (7): the source map of the restricted groupoid is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionSource_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).s.left)

/- Lemma 79.9.5 (8): the source map of the restricted groupoid is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionSource_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).s.left)

/- Lemma 79.9.5 (9): the source map of the restricted groupoid is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionSource_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).s.left)

/- Lemma 79.9.5 (10): the target map of the restricted groupoid is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionTarget_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).t.left)

/- Lemma 79.9.5 (11): the target map of the restricted groupoid is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionTarget_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).t.left)

/- Lemma 79.9.5 (12): the target map of the restricted groupoid is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictionTarget_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (G.pullback
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).t.left)

/- Lemma 79.9.5 (13): the projection `R ×_{s, U} U' ⟶ R` is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackFst_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullback.fst G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (14): the projection `R ×_{s, U} U' ⟶ R` is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackFst_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullback.fst G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (15): the projection `R ×_{s, U} U' ⟶ R` is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackFst_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullback.fst G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (16): the projection `R ×_{s, U} U' ⟶ U'` is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackSnd_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullback.snd G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (17): the projection `R ×_{s, U} U' ⟶ U'` is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackSnd_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullback.snd G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (18): the projection `R ×_{s, U} U' ⟶ U'` is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.sourcePullbackSnd_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullback.snd G.s
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).left)

/- Lemma 79.9.5 (19): the projection `U' ×_{U, t} R ⟶ U'` is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackFst_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullback.fst
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (20): the projection `U' ×_{U, t} R ⟶ U'` is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackFst_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullback.fst
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (21): the projection `U' ×_{U, t} R ⟶ U'` is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackFst_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullback.fst
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (22): the projection `U' ×_{U, t} R ⟶ R` is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackSnd_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (pullback.snd
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (23): the projection `U' ×_{U, t} R ⟶ R` is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackSnd_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (pullback.snd
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (24): the projection `U' ×_{U, t} R ⟶ R` is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.targetPullbackSnd_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (pullback.snd
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')) G.t).left)

/- Lemma 79.9.5 (25): the field-extension morphism `U' ⟶ U` is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fieldRestriction_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')).left)

/- Lemma 79.9.5 (26): the field-extension morphism `U' ⟶ U` is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fieldRestriction_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')).left)

/- Lemma 79.9.5 (27): the field-extension morphism `U' ⟶ U` is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.fieldRestriction_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k')).left)

end FieldRestriction

section FieldBase

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]

/- Lemma 79.9.5 (28): the source map of a groupoid in algebraic spaces on a field is
surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.source_surjective_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.Surjective G.s.left)

/- Lemma 79.9.5 (29): the source map of a groupoid in algebraic spaces on a field is
flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.source_flat_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.Flat G.s.left)

/- Lemma 79.9.5 (30): the source map of a groupoid in algebraic spaces on a field is
universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.source_universallyOpen_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.UniversallyOpen G.s.left)

/- Lemma 79.9.5 (31): the target map of a groupoid in algebraic spaces on a field is
surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.target_surjective_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.Surjective G.t.left)

/- Lemma 79.9.5 (32): the target map of a groupoid in algebraic spaces on a field is
flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.target_flat_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.Flat G.t.left)

/- Lemma 79.9.5 (33): the target map of a groupoid in algebraic spaces on a field is
universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.target_universallyOpen_of_field G
      (IsOnField.objectSpaceIso G σ) :
    AlgebraicSpace.UniversallyOpen G.t.left)

end FieldBase

section FieldRestrictionArrow

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] (σ : Spec (.of k) ⟶ S) [IsOnField G σ]
variable (k' : Type u) [Field k'] [Algebra k k']

/- Lemma 79.9.5 (34): the arrow component of the restriction morphism is surjective. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom_arrow_surjective G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Surjective (G.pullbackHom
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).arrow.left)

/- Lemma 79.9.5 (35): the arrow component of the restriction morphism is flat. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom_arrow_flat G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Flat (G.pullbackHom
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).arrow.left)

/- Lemma 79.9.5 (36): the arrow component of the restriction morphism is universally open. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom_arrow_universallyOpen G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.UniversallyOpen (G.pullbackHom
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).arrow.left)

/- Lemma 79.9.5 (37): the arrow component of the restriction morphism is affine. -/
@[stacks 06E1] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.pullbackHom_arrow_affine G
      (IsOnField.objectSpaceIso G σ) (algebraMap k k') :
    AlgebraicSpace.Affine (G.pullbackHom
        (fieldRestrictionOfHom G (IsOnField.objectSpaceIso G σ) (algebraMap k k'))).arrow.left)

end FieldRestrictionArrow

end AlgebraicGeometry.GroupoidAlgebraicSpace
