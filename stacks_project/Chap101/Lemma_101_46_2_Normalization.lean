module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import stacks_project.Chap67.Lemma_67_49_5
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap94.Lemma_94_16_2_Presentation
public import stacks_project.Chap94.Theorem_94_17_3
public import stacks_project.Chap100.Lemma_100_9_8_QuotientMap
public import stacks_project.Chap101.Lemma_101_46_1_FiniteComponents

/-!
# Absolute normalization of algebraic stacks

An algebraic stack with finitely many irreducible components on compact opens has a
chosen absolute normalization `normalization X` and a canonical 1-morphism
`normalizationTo X`, obtained by normalizing a chosen surjective smooth scheme atlas,
lifting the kernel-pair groupoid structure maps uniquely through algebraic-space
normalization, and passing to the quotient stack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- A chosen smooth scheme atlas of `X` whose quasi-compact opens have finitely many
irreducible components. -/
def finiteComponentsScheme (X : GroupoidsOver S) [AlgebraicStack X]
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] : Over S :=
  Exists.choose hX.exists_finiteComponents_smoothCover

/-- The chosen finite-components smooth atlas 1-morphism `slice U ⟶ X`. -/
def finiteComponentsAtlas (X : GroupoidsOver S) [AlgebraicStack X]
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    GroupoidsOver.slice (finiteComponentsScheme X) ⟶ X :=
  Exists.choose (Exists.choose_spec hX.exists_finiteComponents_smoothCover)

/-- The chosen finite-components atlas is smooth. -/
instance instSmooth_finiteComponentsAtlas (X : GroupoidsOver S) [AlgebraicStack X]
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Groupoids.Hom.Smooth (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_smoothCover)).1

/-- The chosen finite-components atlas is surjective. -/
instance instSurjective_finiteComponentsAtlas (X : GroupoidsOver S) [AlgebraicStack X]
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Groupoids.Hom.Surjective (finiteComponentsAtlas X) :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_smoothCover)).2.1

/-- The source of the chosen finite-components atlas has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_finiteComponentsScheme
    (X : GroupoidsOver S) [AlgebraicStack X]
    [hX : HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens (finiteComponentsScheme X).left :=
  (Exists.choose_spec (Exists.choose_spec hX.exists_finiteComponents_smoothCover)).2.2

/-- The chosen finite-components atlas source is representable by the algebraic space
`ofOver U`. -/
theorem finiteComponentsSlice_representable (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    IsRepresentableByAlgebraicSpace (GroupoidsOver.slice (finiteComponentsScheme X)) :=
  ⟨AlgebraicSpace.ofOver (finiteComponentsScheme X),
    ⟨(AlgebraicSpace.ofOverSliceEquiv (finiteComponentsScheme X)).symm⟩⟩

/-- The kernel-pair groupoid in algebraic spaces of the chosen finite-components
smooth atlas. -/
def atlasGroupoid (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    GroupoidAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) :=
  groupoid (finiteComponentsAtlas X) (finiteComponentsSlice_representable X)

/-- The kernel-pair groupoid of the chosen finite-components atlas is smooth. -/
instance instSmooth_atlasGroupoid (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    GroupoidAlgebraicSpace.Smooth (atlasGroupoid X) :=
  groupoid_smooth (finiteComponentsAtlas X) (finiteComponentsSlice_representable X)

/-- The object space of the chosen atlas groupoid has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_atlasObject
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens (atlasGroupoid X).U.left :=
  sorry

/-- The arrow space of the chosen atlas groupoid has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_atlasArrow
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens (atlasGroupoid X).R.left :=
  sorry

/-- The composable-arrow space of the atlas groupoid has finitely many irreducible
components on compact opens. -/
instance instHasFiniteIrreducibleComponentsOnCompactOpens_atlasComposable
    (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens
      (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left :=
  sorry

/-- The unique lift of a morphism of algebraic spaces through absolute normalization. -/
def liftNormalization {X Y : AlgebraicSpace S}
    [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⟶ Y) (hf : AlgebraicSpace.mapsCodimZero f) :
    X.normalization ⟶ Y.normalization :=
  Classical.choose
    (ExistsUnique.exists (AlgebraicSpace.Normalization.existsUnique_map f hf))

/-- `liftNormalization f hf` is the unique map satisfying
`g ≫ Y.normalizationTo = X.normalizationTo ≫ f`. -/
theorem liftNormalization_comp {X Y : AlgebraicSpace S}
    [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens X]
    [AlgebraicSpace.HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (f : X ⟶ Y) (hf : AlgebraicSpace.mapsCodimZero f) :
    liftNormalization f hf ≫ Y.normalizationTo = X.normalizationTo ≫ f :=
  sorry

/-- The unique lift `s^ν` of the atlas source map through algebraic-space
normalization. -/
def normalizedSource (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).R.left.normalization ⟶
      (atlasGroupoid X).U.left.normalization :=
  liftNormalization (atlasGroupoid X).s.left
    (AlgebraicSpace.mapsCodimZero_of_smooth (atlasGroupoid X).s.left)

/-- `normalizedSource X` lifts `(atlasGroupoid X).s.left` through normalization. -/
theorem normalizedSource_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedSource X ≫ (atlasGroupoid X).U.left.normalizationTo =
      (atlasGroupoid X).R.left.normalizationTo ≫ (atlasGroupoid X).s.left :=
  sorry

/-- The unique lift `t^ν` of the atlas target map through algebraic-space
normalization. -/
def normalizedTarget (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).R.left.normalization ⟶
      (atlasGroupoid X).U.left.normalization :=
  liftNormalization (atlasGroupoid X).t.left
    (AlgebraicSpace.mapsCodimZero_of_smooth (atlasGroupoid X).t.left)

/-- `normalizedTarget X` lifts `(atlasGroupoid X).t.left` through normalization. -/
theorem normalizedTarget_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedTarget X ≫ (atlasGroupoid X).U.left.normalizationTo =
      (atlasGroupoid X).R.left.normalizationTo ≫ (atlasGroupoid X).t.left :=
  sorry

/-- The unique identification of `R^ν` with the one-sided fibre product
`R ×_{s, U} U^ν`. -/
def sourcePullbackIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).R.left.normalization ≅
      pullback (atlasGroupoid X).U.left.normalizationTo (atlasGroupoid X).s.left :=
  Classical.choose
    (ExistsUnique.exists
      (AlgebraicSpace.Normalization.existsUnique_pullbackIso_of_smooth
        (atlasGroupoid X).s.left))

/-- The second projection of `sourcePullbackIso X` recovers `R.normalizationTo`. -/
theorem sourcePullbackIso_snd (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (sourcePullbackIso X).hom ≫
        pullback.snd (atlasGroupoid X).U.left.normalizationTo (atlasGroupoid X).s.left =
      (atlasGroupoid X).R.left.normalizationTo :=
  sorry

/-- The unique identification of `R^ν` with the one-sided fibre product
`U^ν ×_{U, t} R`. -/
def targetPullbackIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).R.left.normalization ≅
      pullback (atlasGroupoid X).U.left.normalizationTo (atlasGroupoid X).t.left :=
  Classical.choose
    (ExistsUnique.exists
      (AlgebraicSpace.Normalization.existsUnique_pullbackIso_of_smooth
        (atlasGroupoid X).t.left))

/-- The second projection of `targetPullbackIso X` recovers `R.normalizationTo`. -/
theorem targetPullbackIso_snd (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (targetPullbackIso X).hom ≫
        pullback.snd (atlasGroupoid X).U.left.normalizationTo (atlasGroupoid X).t.left =
      (atlasGroupoid X).R.left.normalizationTo :=
  sorry

/-- The inverse-arrow map of the atlas groupoid sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_atlasInverse (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.mapsCodimZero (atlasGroupoid X).i.left :=
  sorry

/-- The composition map of the atlas groupoid sends codimension-`0` points to
codimension-`0` points. -/
theorem mapsCodimZero_atlasCompose (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.mapsCodimZero (atlasGroupoid X).c.left :=
  sorry

/-- The commuting witness for the identity section of `R ×_{s, U} U^ν`. -/
theorem normalizedIdentity_lift_w (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    𝟙 (atlasGroupoid X).U.left.normalization ≫
        (atlasGroupoid X).U.left.normalizationTo =
      ((atlasGroupoid X).U.left.normalizationTo ≫ (atlasGroupoid X).e.left) ≫
        (atlasGroupoid X).s.left :=
  sorry

/-- The identity-arrow map `e^ν`, obtained as the section of `s^ν` corresponding to
`e` under `R^ν ≅ R ×_{s, U} U^ν`. -/
def normalizedIdentity (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).U.left.normalization ⟶
      (atlasGroupoid X).R.left.normalization :=
  pullback.lift (𝟙 _)
      ((atlasGroupoid X).U.left.normalizationTo ≫ (atlasGroupoid X).e.left)
      (normalizedIdentity_lift_w X) ≫
    (sourcePullbackIso X).inv

/-- `normalizedIdentity X` is a section of `normalizedSource X` after composing with
the source-sided pullback identification. -/
theorem normalizedIdentity_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedIdentity X ≫ (atlasGroupoid X).R.left.normalizationTo =
      (atlasGroupoid X).U.left.normalizationTo ≫ (atlasGroupoid X).e.left :=
  sorry

/-- The unique lift `i^ν` of the atlas inverse through algebraic-space
normalization. -/
def normalizedInverse (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (atlasGroupoid X).R.left.normalization ⟶
      (atlasGroupoid X).R.left.normalization :=
  liftNormalization (atlasGroupoid X).i.left (mapsCodimZero_atlasInverse X)

/-- `normalizedInverse X` lifts `(atlasGroupoid X).i.left` through normalization. -/
theorem normalizedInverse_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedInverse X ≫ (atlasGroupoid X).R.left.normalizationTo =
      (atlasGroupoid X).R.left.normalizationTo ≫ (atlasGroupoid X).i.left :=
  sorry

/-- The structure map from composable arrows to the object space, sending a pair to
the common object of the later source and earlier target. -/
def atlasComposableToU (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left ⟶
      (atlasGroupoid X).U.left :=
  (pullback.fst (atlasGroupoid X).s (atlasGroupoid X).t ≫ (atlasGroupoid X).s).left

/-- The map from composable arrows to the atlas object space is smooth. -/
instance instSmooth_atlasComposableToU (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicSpace.Smooth (atlasComposableToU X) :=
  sorry

/-- The unique identification of `(R ×_{s, t} R)^ν` with the one-sided fibre product
along `atlasComposableToU X`. -/
def composablePullbackIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left.normalization ≅
      pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) :=
  Classical.choose
    (ExistsUnique.exists
      (AlgebraicSpace.Normalization.existsUnique_pullbackIso_of_smooth
        (atlasComposableToU X)))

/-- The second projection of `composablePullbackIso X` recovers normalization of the
composable-arrow space. -/
theorem composablePullbackIso_snd (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (composablePullbackIso X).hom ≫
        pullback.snd (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) =
      (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left.normalizationTo :=
  sorry

/-- The object over `S` whose underlying space is the pullback of the atlas source and
target as morphisms of algebraic spaces. -/
def atlasLeftPullbackOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) :=
  Over.mk
    (pullback.fst (atlasGroupoid X).s.left (atlasGroupoid X).t.left ≫
      (atlasGroupoid X).R.hom)

/-- The comparison from the algebraic-space pullback of `s.left` and `t.left` to the
Over-category pullback of `s` and `t`. -/
def atlasLeftPullbackToComposable (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    atlasLeftPullbackOver X ⟶ pullback (atlasGroupoid X).s (atlasGroupoid X).t :=
  pullback.lift
    (Over.homMk (pullback.fst (atlasGroupoid X).s.left (atlasGroupoid X).t.left) rfl)
    (Over.homMk (pullback.snd (atlasGroupoid X).s.left (atlasGroupoid X).t.left) sorry)
    sorry

/-- The underlying algebraic-space map of `atlasLeftPullbackToComposable X`. -/
def atlasComposableLeftInv (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (atlasGroupoid X).s.left (atlasGroupoid X).t.left ⟶
      (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left :=
  (atlasLeftPullbackToComposable X).left

/-- The comparison from the Over-category pullback of `s` and `t` to the
algebraic-space pullback of `s.left` and `t.left`. -/
def atlasComposableLeftHom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left ⟶
      pullback (atlasGroupoid X).s.left (atlasGroupoid X).t.left :=
  pullback.lift (pullback.fst (atlasGroupoid X).s (atlasGroupoid X).t).left
    (pullback.snd (atlasGroupoid X).s (atlasGroupoid X).t).left sorry

/-- The map from `R^ν ×_{s^ν, t^ν} R^ν` to the one-sided fibre product
`(R ×_{s, t} R) ×_U U^ν`. -/
def composableDomainToOneSided (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (normalizedSource X) (normalizedTarget X) ⟶
      pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) :=
  pullback.lift (pullback.fst (normalizedSource X) (normalizedTarget X) ≫
      normalizedSource X)
    (pullback.map (normalizedSource X) (normalizedTarget X)
          (atlasGroupoid X).s.left (atlasGroupoid X).t.left
          (atlasGroupoid X).R.left.normalizationTo
          (atlasGroupoid X).R.left.normalizationTo
          (atlasGroupoid X).U.left.normalizationTo sorry sorry ≫
        atlasComposableLeftInv X)
    sorry

/-- The later-arrow map from `(R ×_{s, t} R) ×_U U^ν` to `R^ν`. -/
def oneSidedLater (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ⟶
      (atlasGroupoid X).R.left.normalization :=
  (pullback.lift
      (pullback.fst (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X))
      (pullback.snd (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ≫
        (pullback.fst (atlasGroupoid X).s (atlasGroupoid X).t).left)
      sorry
      : pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ⟶
          pullback (atlasGroupoid X).U.left.normalizationTo
            (atlasGroupoid X).s.left) ≫
    (sourcePullbackIso X).inv

/-- The earlier-arrow map from `(R ×_{s, t} R) ×_U U^ν` to `R^ν`. -/
def oneSidedEarlier (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ⟶
      (atlasGroupoid X).R.left.normalization :=
  (pullback.lift
      (pullback.fst (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X))
      (pullback.snd (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ≫
        (pullback.snd (atlasGroupoid X).s (atlasGroupoid X).t).left)
      sorry
      : pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ⟶
          pullback (atlasGroupoid X).U.left.normalizationTo
            (atlasGroupoid X).t.left) ≫
    (targetPullbackIso X).inv

/-- The map from the one-sided fibre product `(R ×_{s, t} R) ×_U U^ν` to
`R^ν ×_{s^ν, t^ν} R^ν`. -/
def oneSidedToComposableDomain (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (atlasGroupoid X).U.left.normalizationTo (atlasComposableToU X) ⟶
      pullback (normalizedSource X) (normalizedTarget X) :=
  pullback.lift (oneSidedLater X) (oneSidedEarlier X) sorry

/-- The unique smooth-pullback identification of `R^ν ×_{s^ν, t^ν} R^ν` with
`(R ×_{s, t} R)^ν`. -/
def composableDomainIso (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (normalizedSource X) (normalizedTarget X) ≅
      (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left.normalization where
  hom := composableDomainToOneSided X ≫ (composablePullbackIso X).inv
  inv := (composablePullbackIso X).hom ≫ oneSidedToComposableDomain X
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- `composableDomainIso X` identifies normalized composable arrows with the
normalization of the original composable-arrow space. -/
theorem composableDomainIso_hom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (composableDomainIso X).hom =
      composableDomainToOneSided X ≫ (composablePullbackIso X).inv :=
  sorry

/-- The unique lift `c^ν` of atlas composition through algebraic-space
normalization. -/
def normalizedCompose (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left.normalization ⟶
      (atlasGroupoid X).R.left.normalization :=
  liftNormalization (atlasGroupoid X).c.left (mapsCodimZero_atlasCompose X)

/-- `normalizedCompose X` lifts `(atlasGroupoid X).c.left` through normalization. -/
theorem normalizedCompose_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedCompose X ≫ (atlasGroupoid X).R.left.normalizationTo =
      (pullback (atlasGroupoid X).s (atlasGroupoid X).t).left.normalizationTo ≫
        (atlasGroupoid X).c.left :=
  sorry

/-- The object space of the normalized groupoid, as an object over `S`. -/
def normalizedObject (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) :=
  Over.mk ((atlasGroupoid X).U.left.normalizationTo ≫ (atlasGroupoid X).U.hom)

/-- The arrow space of the normalized groupoid, as an object over `S`. -/
def normalizedArrow (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Over (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) :=
  Over.mk ((atlasGroupoid X).R.left.normalizationTo ≫ (atlasGroupoid X).R.hom)

/-- The source map of the normalized groupoid. -/
def normalizedSourceOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedArrow X ⟶ normalizedObject X :=
  Over.homMk (normalizedSource X) sorry

/-- The target map of the normalized groupoid. -/
def normalizedTargetOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedArrow X ⟶ normalizedObject X :=
  Over.homMk (normalizedTarget X) sorry

/-- The identity-arrow map of the normalized groupoid. -/
def normalizedIdentityOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedObject X ⟶ normalizedArrow X :=
  Over.homMk (normalizedIdentity X) sorry

/-- The inverse-arrow map of the normalized groupoid. -/
def normalizedInverseOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedArrow X ⟶ normalizedArrow X :=
  Over.homMk (normalizedInverse X) sorry

/-- The comparison from the Over-category pullback of `s^ν` and `t^ν` to the
algebraic-space pullback of those maps. -/
def normalizedComposableLeftHom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (pullback (normalizedSourceOver X) (normalizedTargetOver X)).left ⟶
      pullback (normalizedSource X) (normalizedTarget X) :=
  pullback.lift
    (pullback.fst (normalizedSourceOver X) (normalizedTargetOver X)).left
    (pullback.snd (normalizedSourceOver X) (normalizedTargetOver X)).left sorry

/-- The composition map of the normalized groupoid. -/
def normalizedComposeOver (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    pullback (normalizedSourceOver X) (normalizedTargetOver X) ⟶ normalizedArrow X :=
  Over.homMk
    (normalizedComposableLeftHom X ≫
      (composableDomainIso X).hom ≫ normalizedCompose X)
    sorry

/-- The smooth groupoid `(U^ν, R^ν, s^ν, t^ν, c^ν)` obtained by normalizing the
chosen atlas groupoid. -/
def normalizedGroupoid (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    GroupoidAlgebraicSpace (AlgebraicSpace.ofOver (Over.mk (𝟙 S))) where
  U := normalizedObject X
  R := normalizedArrow X
  s := normalizedSourceOver X
  t := normalizedTargetOver X
  c := normalizedComposeOver X
  e := normalizedIdentityOver X
  i := normalizedInverseOver X
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of `normalizedGroupoid X` is the normalization of the atlas
object space, viewed over `S`. -/
theorem normalizedGroupoid_U (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedGroupoid X).U = normalizedObject X :=
  sorry

/-- The normalized atlas groupoid is smooth. -/
instance instSmooth_normalizedGroupoid (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    GroupoidAlgebraicSpace.Smooth (normalizedGroupoid X) :=
  sorry

/-- The morphism of objects over `S` induced by absolute normalization of the atlas
object space. -/
def normalizedObjectTo (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedObject X ⟶ (atlasGroupoid X).U :=
  Over.homMk (atlasGroupoid X).U.left.normalizationTo rfl

/-- The morphism of objects over `S` induced by absolute normalization of the atlas
arrow space. -/
def normalizedArrowTo (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalizedArrow X ⟶ (atlasGroupoid X).R :=
  Over.homMk (atlasGroupoid X).R.left.normalizationTo rfl

/-- The morphism of groupoids in algebraic spaces from the normalized groupoid to
the atlas groupoid, given by the algebraic-space normalization morphisms. -/
def normalizedHom (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Hom (normalizedGroupoid X) (atlasGroupoid X) where
  obj := normalizedObjectTo X
  arrow := normalizedArrowTo X
  map_s := sorry
  map_t := sorry
  map_c := sorry

/-- The object component of `normalizedHom X` is the object-space normalization
morphism over `S`. -/
theorem normalizedHom_obj (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    (normalizedHom X).obj = normalizedObjectTo X :=
  sorry

/-- The absolute normalization `X^ν` of an algebraic stack with finitely many
irreducible components on compact opens. -/
def normalization (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] : GroupoidsOver S :=
  (normalizedGroupoid X).quotientStack

/-- `normalization X` is the quotient stack of the normalized atlas groupoid. -/
theorem normalization_eq (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalization X = (normalizedGroupoid X).quotientStack :=
  sorry

/-- The absolute normalization of an algebraic stack is an algebraic stack. -/
instance instAlgebraicStack_normalization (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    AlgebraicStack (normalization X) :=
  GroupoidAlgebraicSpace.instAlgebraicStack_quotientStack (normalizedGroupoid X)

/-- The canonical absolute normalization 1-morphism `ν : X^ν ⟶ X`. -/
def normalizationTo (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    normalization X ⟶ X :=
  GroupoidAlgebraicSpace.Hom.quotientStackHom (normalizedHom X) ≫
    fCan (finiteComponentsAtlas X) (finiteComponentsSlice_representable X)

/-- The atlas of the normalized groupoid, postcomposed with `normalizationTo X`,
recovers the normalized atlas of `X` up to a 2-isomorphism. -/
theorem normalizationTo_comp (X : GroupoidsOver S) [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Nonempty
      ((normalizedGroupoid X).atlas ≫ normalizationTo X ≅
        AlgebraicSpace.toGroupoids.map (normalizedObjectTo X).left ≫
          (atlasGroupoid X).atlas ≫
            fCan (finiteComponentsAtlas X) (finiteComponentsSlice_representable X)) :=
  sorry

/-- A smooth morphism from a scheme into an algebraic stack with finitely many
irreducible components on compact opens has that property on the source. -/
theorem hasFiniteIrreducibleComponentsOnCompactOpens_of_smoothSlice
    {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    {U : Over S} (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    Scheme.HasFiniteIrreducibleComponentsOnCompactOpens U.left :=
  sorry

/-- The scheme-level absolute normalization of a smooth scheme slice of `X`. -/
def smoothSliceOverNormalization {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] : Over S :=
  -- Local instance justification (search instability): finite components on `U`
  -- is determined by the smooth test morphism `p`, which cannot be recovered from
  -- `U.left` alone for global typeclass search.
  letI := hasFiniteIrreducibleComponentsOnCompactOpens_of_smoothSlice p
  AlgebraicSpace.overNormalization U

/-- The morphism over `S` induced by scheme-level absolute normalization of a smooth
scheme slice of `X`. -/
def smoothSliceOverNormalizationTo {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    smoothSliceOverNormalization U p ⟶ U :=
  -- Local instance justification (search instability): finite components on `U`
  -- is determined by the smooth test morphism `p`, which cannot be recovered from
  -- `U.left` alone for global typeclass search.
  letI := hasFiniteIrreducibleComponentsOnCompactOpens_of_smoothSlice p
  AlgebraicSpace.overNormalizationTo U

/-- `smoothSliceOverNormalizationTo U p` is the structure morphism of
`smoothSliceOverNormalization U p` over `U`. -/
theorem smoothSliceOverNormalizationTo_eq {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    (smoothSliceOverNormalizationTo U p).left ≫ U.hom =
      (smoothSliceOverNormalization U p).hom :=
  sorry

/-- The slice 1-morphism induced by scheme-level absolute normalization of a smooth
scheme slice of `X`. -/
def sliceNormalizationHom {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    GroupoidsOver.slice (smoothSliceOverNormalization U p) ⟶
      GroupoidsOver.slice U :=
  (AlgebraicSpace.ofOverSliceEquiv (smoothSliceOverNormalization U p)).inv ≫
    AlgebraicSpace.toGroupoids.map
        (AlgebraicSpace.ofOverMap (smoothSliceOverNormalizationTo U p)) ≫
      (AlgebraicSpace.ofOverSliceEquiv U).hom

/-- `sliceNormalizationHom U p` is the slice 1-morphism of
`smoothSliceOverNormalizationTo U p`. -/
theorem sliceNormalizationHom_eq {X : GroupoidsOver S} [AlgebraicStack X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (U : Over S) (p : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth p] :
    sliceNormalizationHom U p =
      (AlgebraicSpace.ofOverSliceEquiv (smoothSliceOverNormalization U p)).inv ≫
        AlgebraicSpace.toGroupoids.map
            (AlgebraicSpace.ofOverMap (smoothSliceOverNormalizationTo U p)) ≫
          (AlgebraicSpace.ofOverSliceEquiv U).hom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
