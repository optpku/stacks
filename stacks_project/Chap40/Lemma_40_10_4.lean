module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Field

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

section FieldRestriction

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k k' : Type u} [Field k] [Field k']
variable (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k')

/- Lemma 40.10.4 (1): the canonical map from the restricted arrows to the source pullback
square is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToSourceSquare_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullbackToSourceSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (2): the canonical map from the restricted arrows to the source pullback
square is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToSourceSquare_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullbackToSourceSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (3): the canonical map from the restricted arrows to the source pullback
square is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToSourceSquare_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullbackToSourceSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (4): the canonical map from the restricted arrows to the target pullback
square is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToTargetSquare_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullbackToTargetSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (5): the canonical map from the restricted arrows to the target pullback
square is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToTargetSquare_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullbackToTargetSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (6): the canonical map from the restricted arrows to the target pullback
square is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackToTargetSquare_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullbackToTargetSquare G (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (7): the source map of the restricted groupoid is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionSource_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (G.pullback (fieldRestriction G eU ι)).s.left)

/- Lemma 40.10.4 (8): the source map of the restricted groupoid is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionSource_flat (G := G) (eU := eU) (ι := ι) :
    Flat (G.pullback (fieldRestriction G eU ι)).s.left)

/- Lemma 40.10.4 (9): the source map of the restricted groupoid is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionSource_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (G.pullback (fieldRestriction G eU ι)).s.left)

/- Lemma 40.10.4 (10): the target map of the restricted groupoid is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionTarget_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (G.pullback (fieldRestriction G eU ι)).t.left)

/- Lemma 40.10.4 (11): the target map of the restricted groupoid is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionTarget_flat (G := G) (eU := eU) (ι := ι) :
    Flat (G.pullback (fieldRestriction G eU ι)).t.left)

/- Lemma 40.10.4 (12): the target map of the restricted groupoid is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.restrictionTarget_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (G.pullback (fieldRestriction G eU ι)).t.left)

/- Lemma 40.10.4 (13): the projection `R ×_{s, U} U' ⟶ R` is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackFst_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullback.fst G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (14): the projection `R ×_{s, U} U' ⟶ R` is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackFst_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullback.fst G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (15): the projection `R ×_{s, U} U' ⟶ R` is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackFst_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullback.fst G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (16): the projection `R ×_{s, U} U' ⟶ U'` is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackSnd_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullback.snd G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (17): the projection `R ×_{s, U} U' ⟶ U'` is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackSnd_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullback.snd G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (18): the projection `R ×_{s, U} U' ⟶ U'` is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.sourcePullbackSnd_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullback.snd G.s (fieldRestriction G eU ι)).left)

/- Lemma 40.10.4 (19): the projection `U' ×_{U, t} R ⟶ U'` is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackFst_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullback.fst (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (20): the projection `U' ×_{U, t} R ⟶ U'` is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackFst_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullback.fst (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (21): the projection `U' ×_{U, t} R ⟶ U'` is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackFst_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullback.fst (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (22): the projection `U' ×_{U, t} R ⟶ R` is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackSnd_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (pullback.snd (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (23): the projection `U' ×_{U, t} R ⟶ R` is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackSnd_flat (G := G) (eU := eU) (ι := ι) :
    Flat (pullback.snd (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (24): the projection `U' ×_{U, t} R ⟶ R` is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.targetPullbackSnd_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (pullback.snd (fieldRestriction G eU ι) G.t).left)

/- Lemma 40.10.4 (25): the field-extension morphism `U' ⟶ U` is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.fieldRestriction_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (fieldRestriction G eU ι).left)

/- Lemma 40.10.4 (26): the field-extension morphism `U' ⟶ U` is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.fieldRestriction_flat (G := G) (eU := eU) (ι := ι) :
    Flat (fieldRestriction G eU ι).left)

/- Lemma 40.10.4 (27): the field-extension morphism `U' ⟶ U` is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.fieldRestriction_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (fieldRestriction G eU ι).left)

end FieldRestriction

section FieldBase

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k : Type u} [Field k]

/- Lemma 40.10.4 (28): the source map of a groupoid scheme over a field is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.source_surjective_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → Surjective G.s.left)

/- Lemma 40.10.4 (29): the source map of a groupoid scheme over a field is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.source_flat_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → Flat G.s.left)

/- Lemma 40.10.4 (30): the source map of a groupoid scheme over a field is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.source_universallyOpen_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → UniversallyOpen G.s.left)

/- Lemma 40.10.4 (31): the target map of a groupoid scheme over a field is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.target_surjective_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → Surjective G.t.left)

/- Lemma 40.10.4 (32): the target map of a groupoid scheme over a field is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.target_flat_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → Flat G.t.left)

/- Lemma 40.10.4 (33): the target map of a groupoid scheme over a field is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.target_universallyOpen_of_field G :
    (Spec (CommRingCat.of k) ≅ G.U.left) → UniversallyOpen G.t.left)

end FieldBase

section FieldRestrictionArrow

variable {S : Scheme.{u}} (G : GroupoidScheme S)
variable {k k' : Type u} [Field k] [Field k']
variable (eU : Spec (CommRingCat.of k) ≅ G.U.left) (ι : k →+* k')

/- Lemma 40.10.4 (34): the arrow component of the restriction morphism is surjective. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom_arrow_surjective (G := G) (eU := eU) (ι := ι) :
    Surjective (G.pullbackHom (fieldRestriction G eU ι)).arrow.left)

/- Lemma 40.10.4 (35): the arrow component of the restriction morphism is flat. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom_arrow_flat (G := G) (eU := eU) (ι := ι) :
    Flat (G.pullbackHom (fieldRestriction G eU ι)).arrow.left)

/- Lemma 40.10.4 (36): the arrow component of the restriction morphism is universally open. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom_arrow_universallyOpen (G := G) (eU := eU) (ι := ι) :
    UniversallyOpen (G.pullbackHom (fieldRestriction G eU ι)).arrow.left)

/- Lemma 40.10.4 (37): the arrow component of the restriction morphism is affine. -/
@[stacks 04LQ] #check
  (AlgebraicGeometry.GroupoidScheme.pullbackHom_arrow_affine (G := G) (eU := eU) (ι := ι) :
    IsAffineHom (G.pullbackHom (fieldRestriction G eU ι)).arrow.left)

end FieldRestrictionArrow

end AlgebraicGeometry.GroupoidScheme
