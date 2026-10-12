/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap70.«70_4_1_1_Comparison»
public import stacks_project.Chap76.Definition_76_9_1_FiniteOrder
public import stacks_project.Chap76.Definition_76_12_1_Neighbourhood
public import stacks_project.Chap88.Definition_88_18_1_Affine

/-!
# Infinitesimal stages of a locally Noetherian formal algebraic space

The canonical `ℕ`-diagram of infinitesimal neighbourhoods of `X_red` in a
locally Noetherian formal algebraic space `X`, as locally Noetherian algebraic
spaces with finite-order thickening transitions. Lean object `n` is cut out by
`I^{n+1} = 0`, so Stacks `X_1 = X_red` is object `0` and Stacks `X_{n+1}` is
object `n`. For `n ≤ m`, object `n` is the `n`th infinitesimal neighbourhood of
object `0` inside object `m`.

The reusable `ℕ`-diagram is cut out inside `X` by vanishing of `I^{n+1}` on
the reduction pullback. Neighbourhood comparison with object `0` inside
object `m` uses Chap76 `Hom.InfinitesimalNeighbourhood.space`, not a second
copy of that owner. This module uses the Affine
`IsFormalAlgebraicSpace`/`IsLocallyNoetherian`/`pullbackHom` interface and a
source-faithful `Reduction` class on that owner.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

/-- The scheme property `IsReduced` is local for the étale precoverage. -/
instance instIsLocal_isReduced_etale :
    ObjectProperty.IsLocal (IsReduced : ObjectProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  sorry

namespace AlgebraicGeometry.FormalAlgebraicSpace

variable {S : Scheme.{u}}

/-- The algebraic-space reduction of a formal algebraic space: a reduced
algebraic space, a representable thickening into the formal algebraic space,
and unique factorization of morphisms from reduced algebraic spaces. -/
class Reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] where
  /-- The underlying reduced algebraic space `X_red`. -/
  space : AlgebraicSpace S
  /-- The representable thickening `X_red ⟶ X`. -/
  ι : space.functorOfPoints ⟶ X
  /-- The reduction is reduced in the étale-local sense. -/
  isReduced : AlgebraicSpace.hasEtaleLocal
    (IsReduced : ObjectProperty Scheme.{u}) space
  /-- The structure morphism is representable by algebraic spaces. -/
  representable : AlgebraicSpace.representableByAlgebraicSpaces ι
  /-- Yoneda pullbacks of the structure morphism are thickenings. -/
  isThickening : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
    AlgebraicSpace.IsThickening
      (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom representable ξ)
  /-- A morphism from a reduced algebraic space into `X` factors uniquely
  through the reduction. -/
  liftUnique {U : AlgebraicSpace S}
    (hU : AlgebraicSpace.hasEtaleLocal
      (IsReduced : ObjectProperty Scheme.{u}) U)
    (g : U.functorOfPoints ⟶ X) :
    ∃! h : U.functorOfPoints ⟶ space.functorOfPoints, h ≫ ι = g

/-- A reduced affine scheme over `S`, viewed as a formal algebraic space, is its
own reduction. -/
instance instReduction_yoneda (U : Over S)
    [AlgebraicGeometry.IsAffine U.left] [IsReduced U.left] :
    Reduction (yoneda.obj U) where
  space := AlgebraicSpace.ofOver U
  ι := 𝟙 _
  isReduced := sorry
  representable := sorry
  isThickening := sorry
  liftUnique := sorry

/-- The algebraic-space reduction of a formal algebraic space. -/
abbrev reduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : AlgebraicSpace S :=
  R.space

/-- The algebraic-space reduction is the `space` field of `Reduction`. -/
theorem reduction_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reduction X = R.space :=
  rfl

/-- The canonical morphism from the reduction of a formal algebraic space. -/
abbrev reductionι (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : (reduction X).functorOfPoints ⟶ X :=
  R.ι

/-- The reduction morphism is the `ι` field of `Reduction`. -/
theorem reductionι_def (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] : reductionι X = R.ι :=
  rfl

/-- The reduction is reduced, the structure morphism is a representable
thickening, and maps from reduced algebraic spaces factor uniquely through
it. -/
theorem Reduction.spec (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [R : Reduction X] :
    AlgebraicSpace.hasEtaleLocal
        (IsReduced : ObjectProperty Scheme.{u}) (reduction X) ∧
      AlgebraicSpace.representableByAlgebraicSpaces (reductionι X) ∧
        (∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ X),
          AlgebraicSpace.IsThickening
            (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
              R.representable ξ)) ∧
          ∀ {U : AlgebraicSpace S},
            AlgebraicSpace.hasEtaleLocal
                (IsReduced : ObjectProperty Scheme.{u}) U →
              ∀ g : U.functorOfPoints ⟶ X,
                ∃! h : U.functorOfPoints ⟶ (reduction X).functorOfPoints,
                  h ≫ reductionι X = g :=
  sorry

/-- A morphism `ξ : T ⟶ X` from a scheme over `S` factors through the `n`th
infinitesimal stage of `X` when `X_red ×_X T ⟶ T` is an `n`th-order
thickening, i.e. when `I^{n+1} = 0` for the ideal sheaf of that closed
immersion. -/
def factorsThroughStage {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [R : Reduction X] (n : ℕ) {U : Over S} (ξ : yoneda.obj U ⟶ X) : Prop :=
  AlgebraicSpace.IsNthOrderThickening n
    (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable ξ)

/-- Factoring through the `n`th infinitesimal stage is `n`th-order thickening of
the reduction pullback. -/
theorem factorsThroughStage_iff {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [R : Reduction X] (n : ℕ) {U : Over S}
    (ξ : yoneda.obj U ⟶ X) :
    factorsThroughStage n ξ ↔
      AlgebraicSpace.IsNthOrderThickening n
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
          R.representable ξ) :=
  Iff.rfl

/-- Restriction of a test morphism along a map of schemes preserves factoring
through an infinitesimal stage. -/
theorem factorsThroughStage_map {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] (n : ℕ) {T T' : (Over S)ᵒᵖ}
    (φ : T ⟶ T') {x : X.obj T}
    (hx : factorsThroughStage n (yonedaEquiv.symm x)) :
    factorsThroughStage n (yonedaEquiv.symm (X.map φ x)) :=
  sorry

/-- If a morphism factors through stage `n` and `n ≤ m`, then it factors through
stage `m`. -/
theorem factorsThroughStage_of_le {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] {n m : ℕ} (hnm : n ≤ m)
    {U : Over S} {ξ : yoneda.obj U ⟶ X} (hξ : factorsThroughStage n ξ) :
    factorsThroughStage m ξ :=
  sorry

/-- Points of the reduction, composed with `reductionι X`, factor through every
infinitesimal stage. -/
theorem factorsThroughStage_of_reduction {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [Reduction X] (n : ℕ) {T : (Over S)ᵒᵖ}
    (y : (reduction X).functorOfPoints.obj T) :
    factorsThroughStage n (yonedaEquiv.symm ((reductionι X).app T y)) :=
  sorry

/-- The subfunctor of `X` whose `T`-points are morphisms `T ⟶ X` that factor
through the `n`th infinitesimal stage. -/
def stageFunctor (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [Reduction X] (n : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {x : X.obj T // factorsThroughStage n (yonedaEquiv.symm x)}
  map φ := TypeCat.ofHom fun x ↦ ⟨X.map φ x.val, factorsThroughStage_map n φ x.property⟩
  map_id := sorry
  map_comp := sorry

/-- The value of `stageFunctor X n` at a test object is the subtype of points
factoring through stage `n`. -/
theorem stageFunctor_obj (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [Reduction X] (n : ℕ) (T : (Over S)ᵒᵖ) :
    (stageFunctor X n).obj T =
      {x : X.obj T // factorsThroughStage n (yonedaEquiv.symm x)} :=
  rfl

/-- A `T`-point of `X` lies on `stageFunctor X n` if and only if it factors
through the `n`th infinitesimal stage. -/
theorem mem_stageFunctor {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [Reduction X] {n : ℕ} {T : (Over S)ᵒᵖ} {x : X.obj T} :
    (∃ p : (stageFunctor X n).obj T, p.val = x) ↔
      factorsThroughStage n (yonedaEquiv.symm x) :=
  sorry

/-- The `n`th infinitesimal stage of the reduction of `X` is an algebraic
space. -/
instance instIsAlgebraicSpace_stageFunctor (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [Reduction X] (n : ℕ) :
    AlgebraicSpace.IsAlgebraicSpace (stageFunctor X n) :=
  sorry

/-- The `n`th infinitesimal neighbourhood of `X_red` in `X`, as an algebraic
space over `S`. Lean object `n` is cut out by `I^{n+1} = 0`, matching
`IsNthOrderThickening n`. -/
def infinitesimalStage (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (n : ℕ) : AlgebraicSpace S :=
  AlgebraicSpace.ofIsAlgebraicSpace (stageFunctor X n)

/-- The functor of points of `infinitesimalStage X n` is `stageFunctor X n`. -/
theorem infinitesimalStage_functorOfPoints (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    (infinitesimalStage X n).functorOfPoints = stageFunctor X n :=
  rfl

/-- The canonical morphism from the `n`th infinitesimal stage to `X`. -/
def stageι (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    (infinitesimalStage X n).functorOfPoints ⟶ X where
  app T := TypeCat.ofHom fun x ↦ x.val
  naturality := sorry

/-- On `T`-points, `stageι X n` forgets the factoring witness. -/
theorem stageι_app (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (n : ℕ) (T : (Over S)ᵒᵖ)
    (x : (infinitesimalStage X n).functorOfPoints.obj T) :
    (stageι X n).app T x = x.val :=
  sorry

/-- The transition morphism of infinitesimal stages for `n ≤ m`. -/
def stageHom (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage X n ⟶ infinitesimalStage X m where
  app T := TypeCat.ofHom fun x ↦ ⟨x.val, factorsThroughStage_of_le hnm x.property⟩
  naturality := sorry

/-- The canonical immersion of Lean object `0` into object `m`. -/
def stageHomZero (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (m : ℕ) :
    infinitesimalStage X 0 ⟶ infinitesimalStage X m :=
  stageHom X (Nat.zero_le m)

/-- `stageHomZero X m` is the stage transition along `0 ≤ m`. -/
theorem stageHomZero_eq (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (m : ℕ) :
    stageHomZero X m = stageHom X (Nat.zero_le m) :=
  rfl

/-- The canonical map `X_red ⟶ X_n` over `X`. -/
def fromReduction (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    reduction X ⟶ infinitesimalStage X n where
  app T := TypeCat.ofHom fun y ↦
    ⟨(reductionι X).app T y, factorsThroughStage_of_reduction n y⟩
  naturality := sorry

/-- The diagram of infinitesimal stages, indexed by `ℕ`. -/
def infinitesimalStages (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] : ℕ ⥤ AlgebraicSpace S where
  obj n := infinitesimalStage X n
  map f := stageHom X (leOfHom f)
  map_id := sorry
  map_comp := sorry

/-- Objects of `infinitesimalStages X` are the infinitesimal stages. -/
theorem infinitesimalStages_obj (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    (infinitesimalStages X).obj n = infinitesimalStage X n :=
  rfl

/-- Transition maps of `infinitesimalStages X` are `stageHom`. -/
theorem infinitesimalStages_map (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (f : n ⟶ m) :
    (infinitesimalStages X).map f = stageHom X (leOfHom f) :=
  rfl

/-- Stage inclusions are compatible with the canonical maps to `X`. -/
theorem stageι_comp (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    AlgebraicSpace.forgetToPresheaf.map (stageHom X hnm) ≫ stageι X m =
      stageι X n :=
  sorry

/-- The reduction triangle: `fromReduction X n` then `stageι X n` recovers
`reductionι X`. -/
theorem fromReduction_comp_stageι (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    AlgebraicSpace.forgetToPresheaf.map (fromReduction X n) ≫ stageι X n =
      reductionι X :=
  sorry

/-- The cocone of infinitesimal stages with vertex `X`. -/
def infinitesimalCocone (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] :
    Cocone (infinitesimalStages X ⋙ AlgebraicSpace.forgetToPresheaf) where
  pt := X
  ι :=
    { app n := stageι X n
      naturality := sorry }

/-- Components of `infinitesimalCocone X` are the morphisms `stageι X n`. -/
theorem infinitesimalCocone_ι (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    (infinitesimalCocone X).ι.app n = stageι X n :=
  rfl

/-- The canonical map from the reduction to the `n`th infinitesimal stage is an
`n`th-order thickening. -/
instance instIsNthOrderThickening_fromReduction (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    AlgebraicSpace.IsNthOrderThickening n (fromReduction X n) :=
  sorry

/-- The transition from stage `0` to stage `m` is a closed immersion. -/
instance instIsClosedImmersion_stageHomZero (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] (m : ℕ) :
    AlgebraicSpace.IsClosedImmersion (stageHomZero X m) :=
  sorry

/-- Composing the stage-`0` map with `stageι X 0` recovers `reductionι X`. -/
theorem infinitesimalStage_zero_comp_stageι (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X] :
    AlgebraicSpace.forgetToPresheaf.map (fromReduction X 0) ≫ stageι X 0 =
      reductionι X :=
  sorry

/-- A stage-`n` point, viewed in stage `m`, lifts uniquely along the coborder
open immersion of `stageHomZero X m`. -/
theorem exists_liftAlongCoborderRange (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) {T : (Over S)ᵒᵖ}
    (x : (infinitesimalStage X n).functorOfPoints.obj T) :
    ∃ z : (AlgebraicSpace.IsImmersion.coborderRange (stageHomZero X m)).X.functorOfPoints.obj T,
      (AlgebraicSpace.IsImmersion.coborderRange (stageHomZero X m)).ι.app T z =
        (stageHom X hnm).app T x :=
  sorry

/-- The coborder lift of a stage-`n` point along `coborderRange.ι` of
`stageHomZero X m`. -/
def liftAlongCoborderRange (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) {T : (Over S)ᵒᵖ}
    (x : (infinitesimalStage X n).functorOfPoints.obj T) :
    (AlgebraicSpace.IsImmersion.coborderRange (stageHomZero X m)).X.functorOfPoints.obj T :=
  Classical.choose (exists_liftAlongCoborderRange X hnm x)

/-- The coborder lift of a stage-`n` point maps to the corresponding stage-`m`
point under `coborderRange.ι`. -/
theorem liftAlongCoborderRange_app (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) {T : (Over S)ᵒᵖ}
    (x : (infinitesimalStage X n).functorOfPoints.obj T) :
    (AlgebraicSpace.IsImmersion.coborderRange (stageHomZero X m)).ι.app T
        (liftAlongCoborderRange X hnm x) =
      (stageHom X hnm).app T x :=
  sorry

/-- The comparison morphism from Lean object `n` to the Chap76 neighbourhood of
object `0` inside object `m`. On `T`-points it sends a stage-`n` point `x` to
the neighbourhood point whose `toAmbient` image is `(stageHom X hnm).app T x`,
by lifting that stage-`m` point along `coborderRange.ι` and recording that
`ideal (stageHomZero X m) n` vanishes. -/
def infinitesimalStageIsoNeighbourhood_hom (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage X n ⟶
      AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space (stageHomZero X m) n where
  app T :=
    TypeCat.ofHom fun x ↦
      (⟨liftAlongCoborderRange X hnm x, sorry⟩ :
        (AlgebraicSpace.subschemeFunctor
          (AlgebraicSpace.Hom.InfinitesimalNeighbourhood.ideal
            (stageHomZero X m) n)).obj T)
  naturality := sorry

/-- The inverse comparison from the Chap76 neighbourhood of object `0` inside
object `m` back to Lean object `n`. -/
def infinitesimalStageIsoNeighbourhood_inv (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) :
    AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space (stageHomZero X m) n ⟶
      infinitesimalStage X n where
  app T :=
    TypeCat.ofHom fun y =>
      ⟨(stageι X m).app T
          ((AlgebraicSpace.Hom.InfinitesimalNeighbourhood.toAmbient
              (stageHomZero X m) n).app T y),
        sorry⟩
  naturality := sorry

/-- For `n ≤ m`, Lean object `n` is the `n`th infinitesimal neighbourhood of
object `0` inside object `m`. Stacks `X_{n+1}` is this Lean object `n`. -/
def infinitesimalStageIsoNeighbourhood (X : (Over S)ᵒᵖ ⥤ Type u)
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] [Reduction X]
    {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage X n ≅
      AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space (stageHomZero X m) n where
  hom := infinitesimalStageIsoNeighbourhood_hom X hnm
  inv := infinitesimalStageIsoNeighbourhood_inv X hnm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The source triangle: `fromReduction X 0` into the Chap76 neighbourhood
equals `fromReduction X n` followed by the comparison isomorphism. -/
theorem infinitesimalStageIsoNeighbourhood_fromSource
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    fromReduction X 0 ≫
        AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource
          (stageHomZero X m) n =
      fromReduction X n ≫ (infinitesimalStageIsoNeighbourhood X hnm).hom :=
  sorry

/-- The ambient triangle: the comparison isomorphism followed by `toAmbient`
recovers `stageHom X hnm`. -/
theorem infinitesimalStageIsoNeighbourhood_toAmbient
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    (infinitesimalStageIsoNeighbourhood X hnm).hom ≫
        AlgebraicSpace.Hom.InfinitesimalNeighbourhood.toAmbient
          (stageHomZero X m) n =
      stageHom X hnm :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
