module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

/-!
# Field-homomorphism restriction of groupoids in algebraic spaces

This module records the restriction of a groupoid in algebraic spaces along an
explicit field homomorphism `ι : k →+* k'` of its object space, together with
the induced identification of the restricted object space with `Spec(k')`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism `Spec(k') ⟶ U` of algebraic spaces induced by a field homomorphism
`ι : k →+* k'` and an identification `U ≅ Spec(k)` over `S`. -/
abbrev fieldRestrictionOfHomMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    ofOver (Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ σ)) ⟶ G.U.left :=
  ofOverHomMk (Spec.map (CommRingCat.ofHom ι)) rfl ≫ eU.inv

/-- The object space over `B` obtained by extending the field of objects along `ι`. -/
abbrev fieldRestrictionOfHomOver {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    Over B :=
  Over.mk (fieldRestrictionOfHomMap G eU ι ≫ G.U.hom)

/-- The canonical morphism over `B` from the field-homomorphism object space to the
original object space. -/
abbrev fieldRestrictionOfHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    fieldRestrictionOfHomOver G eU ι ⟶ G.U :=
  Over.homMk (fieldRestrictionOfHomMap G eU ι) rfl

/-- The underlying algebraic-space map of `fieldRestrictionOfHom` is
`fieldRestrictionOfHomMap`. -/
theorem fieldRestrictionOfHom_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    (fieldRestrictionOfHom G eU ι).left = fieldRestrictionOfHomMap G eU ι :=
  rfl

/-- The restricted object space is `Spec(k')` as an algebraic space over `S`. -/
theorem fieldRestrictionOfHomOver_left {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {k k' : Type u} [Field k] [Field k']
    {σ : Spec (.of k) ⟶ S} (eU : G.U.left ≅ ofOver (Over.mk σ)) (ι : k →+* k') :
    (fieldRestrictionOfHomOver G eU ι).left =
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom ι) ≫ σ)) :=
  rfl

section FieldRestriction

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k k' : Type u} [Field k] [Field k'] {σ : Spec (.of k) ⟶ S}
variable (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) (ι : k →+* k')

/-- The field-extension morphism `U' ⟶ U` is affine. -/
theorem fieldRestriction_affine :
    AlgebraicSpace.Affine (fieldRestrictionOfHom G eU ι).left :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
surjective. -/
theorem pullbackToSourceSquare_surjective :
    AlgebraicSpace.Surjective (pullbackToSourceSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
flat. -/
theorem pullbackToSourceSquare_flat :
    AlgebraicSpace.Flat (pullbackToSourceSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The canonical map from the restricted arrows to the source pullback square is
universally open. -/
theorem pullbackToSourceSquare_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullbackToSourceSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
surjective. -/
theorem pullbackToTargetSquare_surjective :
    AlgebraicSpace.Surjective (pullbackToTargetSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
flat. -/
theorem pullbackToTargetSquare_flat :
    AlgebraicSpace.Flat (pullbackToTargetSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The canonical map from the restricted arrows to the target pullback square is
universally open. -/
theorem pullbackToTargetSquare_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullbackToTargetSquare G (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The source map of the restricted groupoid is surjective. -/
theorem restrictionSource_surjective :
    AlgebraicSpace.Surjective (G.pullback (fieldRestrictionOfHom G eU ι)).s.left :=
  sorry

/-- The source map of the restricted groupoid is flat. -/
theorem restrictionSource_flat :
    AlgebraicSpace.Flat (G.pullback (fieldRestrictionOfHom G eU ι)).s.left :=
  sorry

/-- The source map of the restricted groupoid is universally open. -/
theorem restrictionSource_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullback (fieldRestrictionOfHom G eU ι)).s.left :=
  sorry

/-- The target map of the restricted groupoid is surjective. -/
theorem restrictionTarget_surjective :
    AlgebraicSpace.Surjective (G.pullback (fieldRestrictionOfHom G eU ι)).t.left :=
  sorry

/-- The target map of the restricted groupoid is flat. -/
theorem restrictionTarget_flat :
    AlgebraicSpace.Flat (G.pullback (fieldRestrictionOfHom G eU ι)).t.left :=
  sorry

/-- The target map of the restricted groupoid is universally open. -/
theorem restrictionTarget_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullback (fieldRestrictionOfHom G eU ι)).t.left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is surjective. -/
theorem sourcePullbackFst_surjective :
    AlgebraicSpace.Surjective (pullback.fst G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is flat. -/
theorem sourcePullbackFst_flat :
    AlgebraicSpace.Flat (pullback.fst G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ R` is universally open. -/
theorem sourcePullbackFst_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.fst G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is surjective. -/
theorem sourcePullbackSnd_surjective :
    AlgebraicSpace.Surjective (pullback.snd G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is flat. -/
theorem sourcePullbackSnd_flat :
    AlgebraicSpace.Flat (pullback.snd G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `R ×_{s, U} U' ⟶ U'` is universally open. -/
theorem sourcePullbackSnd_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.snd G.s (fieldRestrictionOfHom G eU ι)).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is surjective. -/
theorem targetPullbackFst_surjective :
    AlgebraicSpace.Surjective (pullback.fst (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is flat. -/
theorem targetPullbackFst_flat :
    AlgebraicSpace.Flat (pullback.fst (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ U'` is universally open. -/
theorem targetPullbackFst_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.fst (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is surjective. -/
theorem targetPullbackSnd_surjective :
    AlgebraicSpace.Surjective (pullback.snd (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is flat. -/
theorem targetPullbackSnd_flat :
    AlgebraicSpace.Flat (pullback.snd (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The projection `U' ×_{U, t} R ⟶ R` is universally open. -/
theorem targetPullbackSnd_universallyOpen :
    AlgebraicSpace.UniversallyOpen (pullback.snd (fieldRestrictionOfHom G eU ι) G.t).left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is surjective. -/
theorem fieldRestriction_surjective :
    AlgebraicSpace.Surjective (fieldRestrictionOfHom G eU ι).left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is flat. -/
theorem fieldRestriction_flat :
    AlgebraicSpace.Flat (fieldRestrictionOfHom G eU ι).left :=
  sorry

/-- The field-extension morphism `U' ⟶ U` is universally open. -/
theorem fieldRestriction_universallyOpen :
    AlgebraicSpace.UniversallyOpen (fieldRestrictionOfHom G eU ι).left :=
  sorry

end FieldRestriction

section FieldBase

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k : Type u} [Field k] {σ : Spec (.of k) ⟶ S}

/-- The source map of a groupoid in algebraic spaces on a field is surjective. -/
theorem source_surjective_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.Surjective G.s.left :=
  sorry

/-- The source map of a groupoid in algebraic spaces on a field is flat. -/
theorem source_flat_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.Flat G.s.left :=
  sorry

/-- The source map of a groupoid in algebraic spaces on a field is universally open. -/
theorem source_universallyOpen_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.UniversallyOpen G.s.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is surjective. -/
theorem target_surjective_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.Surjective G.t.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is flat. -/
theorem target_flat_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.Flat G.t.left :=
  sorry

/-- The target map of a groupoid in algebraic spaces on a field is universally open. -/
theorem target_universallyOpen_of_field
    (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) :
    AlgebraicSpace.UniversallyOpen G.t.left :=
  sorry

end FieldBase

section FieldRestrictionArrow

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable {k k' : Type u} [Field k] [Field k'] {σ : Spec (.of k) ⟶ S}
variable (eU : G.U.left ≅ AlgebraicSpace.ofOver (Over.mk σ)) (ι : k →+* k')

/-- The arrow component of the restriction morphism is surjective. -/
theorem pullbackHom_arrow_surjective :
    AlgebraicSpace.Surjective (G.pullbackHom (fieldRestrictionOfHom G eU ι)).arrow.left :=
  sorry

/-- The arrow component of the restriction morphism is flat. -/
theorem pullbackHom_arrow_flat :
    AlgebraicSpace.Flat (G.pullbackHom (fieldRestrictionOfHom G eU ι)).arrow.left :=
  sorry

/-- The arrow component of the restriction morphism is universally open. -/
theorem pullbackHom_arrow_universallyOpen :
    AlgebraicSpace.UniversallyOpen (G.pullbackHom (fieldRestrictionOfHom G eU ι)).arrow.left :=
  sorry

/-- The dotted arrow `R' ⟶ R` is affine. -/
theorem pullbackHom_arrow_affine :
    AlgebraicSpace.Affine (G.pullbackHom (fieldRestrictionOfHom G eU ι)).arrow.left :=
  sorry

end FieldRestrictionArrow

end AlgebraicGeometry.GroupoidAlgebraicSpace
