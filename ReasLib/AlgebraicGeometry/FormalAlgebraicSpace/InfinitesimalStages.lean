/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Types
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.InfinitesimalNeighbourhood

/-!
# Canonical infinitesimal stages of formal algebraic spaces

The stages are the subfunctors defined by vanishing of successive powers of
the pulled-back reduction ideal. Stage `n` uses the power `n + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

variable {S : Scheme.{u}}

/-- A morphism `ξ : T ⟶ X` from a scheme over `S` factors through the `n`th
infinitesimal stage of `X` when `X_red ×_X T ⟶ T` is an `n`th-order
thickening, i.e. when `I^{n+1} = 0` for the ideal sheaf of that closed
immersion. -/
def factorsThroughStage {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X) (n : ℕ) {U : Over S} (ξ : yoneda.obj U ⟶ X) : Prop :=
  AlgebraicSpace.IsNthOrderThickening n
    (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom R.representable ξ)

/-- Factoring through the `n`th infinitesimal stage is `n`th-order thickening of
the reduction pullback. -/
theorem factorsThroughStage_iff {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) (n : ℕ) {U : Over S}
    (ξ : yoneda.obj U ⟶ X) :
    factorsThroughStage R n ξ ↔
      AlgebraicSpace.IsNthOrderThickening n
        (AlgebraicSpace.representableByAlgebraicSpaces.pullbackHom
          R.representable ξ) :=
  Iff.rfl

/-- Restriction of a test morphism along a map of schemes preserves factoring
through an infinitesimal stage. -/
theorem factorsThroughStage_map {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) (n : ℕ) {T T' : (Over S)ᵒᵖ}
    (φ : T ⟶ T') {x : X.obj T}
    (hx : factorsThroughStage R n (yonedaEquiv.symm x)) :
    factorsThroughStage R n (yonedaEquiv.symm (X.map φ x)) :=
  sorry

/-- If a morphism factors through stage `n` and `n ≤ m`, then it factors through
stage `m`. -/
theorem factorsThroughStage_of_le {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m)
    {U : Over S} {ξ : yoneda.obj U ⟶ X} (hξ : factorsThroughStage R n ξ) :
    factorsThroughStage R m ξ :=
  sorry

/-- Points of the reduction, composed with `R.ι`, factor through every
infinitesimal stage. -/
theorem factorsThroughStage_of_reduction {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] (R : ReductionData X) (n : ℕ) {T : (Over S)ᵒᵖ}
    (y : (R.space).functorOfPoints.obj T) :
    factorsThroughStage R n (yonedaEquiv.symm ((R.ι).app T y)) :=
  sorry

/-- The subfunctor of `X` whose `T`-points are morphisms `T ⟶ X` that factor
through the `n`th infinitesimal stage. -/
def stageFunctor {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X) (n : ℕ) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := {x : X.obj T // factorsThroughStage R n (yonedaEquiv.symm x)}
  map φ := TypeCat.ofHom fun x ↦ ⟨X.map φ x.val, factorsThroughStage_map R n φ x.property⟩
  map_id := sorry
  map_comp := sorry

/-- The value of `stageFunctor R n` at a test object is the subtype of points
factoring through stage `n`. -/
theorem stageFunctor_obj {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X) (n : ℕ) (T : (Over S)ᵒᵖ) :
    (stageFunctor R n).obj T =
      {x : X.obj T // factorsThroughStage R n (yonedaEquiv.symm x)} :=
  rfl

/-- A `T`-point of `X` lies on `stageFunctor R n` if and only if it factors
through the `n`th infinitesimal stage. -/
theorem mem_stageFunctor {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    (R : ReductionData X) {n : ℕ} {T : (Over S)ᵒᵖ} {x : X.obj T} :
    (∃ p : (stageFunctor R n).obj T, p.val = x) ↔
      factorsThroughStage R n (yonedaEquiv.symm x) :=
  sorry

/-- The `n`th infinitesimal stage of the reduction of `X` is an algebraic
space. -/
theorem isAlgebraicSpace_stageFunctor {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    AlgebraicSpace.IsAlgebraicSpace (stageFunctor R n) :=
  sorry

/-- The `n`th infinitesimal neighbourhood of `X_red` in `X`, as an algebraic
space over `S`. Stage `n` is cut out by `I^{n+1} = 0`, matching
`IsNthOrderThickening n`. -/
def infinitesimalStage {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) : AlgebraicSpace S :=
  AlgebraicSpace.ofFunctor (stageFunctor R n)
    (isAlgebraicSpace_stageFunctor R n).isSheaf
    (isAlgebraicSpace_stageFunctor R n).representableDiagonal
    (isAlgebraicSpace_stageFunctor R n).atlas

/-- The functor of points of `infinitesimalStage R n` is `stageFunctor R n`. -/
theorem infinitesimalStage_functorOfPoints {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    (infinitesimalStage R n).functorOfPoints = stageFunctor R n :=
  rfl

/-- The canonical morphism from the `n`th infinitesimal stage to `X`. -/
def stageι {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    (infinitesimalStage R n).functorOfPoints ⟶ X where
  app T := TypeCat.ofHom fun x ↦ x.val
  naturality := sorry

/-- On `T`-points, `stageι R n` forgets the factoring witness. -/
theorem stageι_app {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) (T : (Over S)ᵒᵖ)
    (x : (infinitesimalStage R n).functorOfPoints.obj T) :
    (stageι R n).app T x = x.val :=
  rfl

/-- The transition morphism of infinitesimal stages for `n ≤ m`. -/
def stageHom {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage R n ⟶ infinitesimalStage R m where
  app T := TypeCat.ofHom fun x ↦ ⟨x.val, factorsThroughStage_of_le R hnm x.property⟩
  naturality := sorry

/-- The canonical immersion of Lean object `0` into object `m`. -/
def stageHomZero {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) (m : ℕ) :
    infinitesimalStage R 0 ⟶ infinitesimalStage R m :=
  stageHom R (Nat.zero_le m)

/-- `stageHomZero R m` is the stage transition along `0 ≤ m`. -/
theorem stageHomZero_eq {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (m : ℕ) :
    stageHomZero R m = stageHom R (Nat.zero_le m) :=
  rfl

/-- The canonical map `X_red ⟶ X_n` over `X`. -/
def fromReduction {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    R.space ⟶ infinitesimalStage R n where
  app T := TypeCat.ofHom fun y ↦
    ⟨(R.ι).app T y, factorsThroughStage_of_reduction R n y⟩
  naturality := sorry

/-- The diagram of infinitesimal stages, indexed by `ℕ`. -/
def infinitesimalStages {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) : ℕ ⥤ AlgebraicSpace S where
  obj n := infinitesimalStage R n
  map f := stageHom R (leOfHom f)
  map_id := sorry
  map_comp := sorry

/-- Objects of `infinitesimalStages R` are the infinitesimal stages. -/
theorem infinitesimalStages_obj {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    (infinitesimalStages R).obj n = infinitesimalStage R n :=
  rfl

/-- Transition maps of `infinitesimalStages R` are `stageHom`. -/
theorem infinitesimalStages_map {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X)
    {n m : ℕ} (f : n ⟶ m) :
    (infinitesimalStages R).map f = stageHom R (leOfHom f) :=
  rfl

/-- Stage inclusions are compatible with the canonical maps to `X`. -/
theorem stageι_comp {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    AlgebraicSpace.forgetToPresheaf.map (stageHom R hnm) ≫ stageι R m =
      stageι R n :=
  sorry

/-- The reduction triangle: `fromReduction R n` then `stageι R n` recovers
`R.ι`. -/
theorem fromReduction_comp_stageι {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    AlgebraicSpace.forgetToPresheaf.map (fromReduction R n) ≫ stageι R n =
      R.ι :=
  sorry

/-- The cocone of infinitesimal stages with vertex `X`. -/
def infinitesimalCocone {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) :
    Cocone (infinitesimalStages R ⋙ AlgebraicSpace.forgetToPresheaf) where
  pt := X
  ι :=
    { app n := stageι R n
      naturality := sorry }

/-- Components of `infinitesimalCocone R` are the morphisms `stageι R n`. -/
theorem infinitesimalCocone_ι {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    (infinitesimalCocone R).ι.app n = stageι R n :=
  rfl

/-- The canonical map from the reduction to the `n`th infinitesimal stage is an
`n`th-order thickening. -/
theorem isNthOrderThickening_fromReduction {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    AlgebraicSpace.IsNthOrderThickening n (fromReduction R n) :=
  sorry

/-- The transition from stage `0` to stage `m` is a closed immersion. -/
theorem isClosedImmersion_stageHomZero {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (m : ℕ) :
    AlgebraicSpace.IsClosedImmersion (stageHomZero R m) :=
  sorry

/-- The canonical infinitesimal neighbourhood of stage zero inside stage `m`. -/
def neighbourhoodSpace {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) (m n : ℕ) : AlgebraicSpace S := by
  -- Local instance justification (defeq pin): Pin the proof-class dictionary for this fixed stage immersion so the canonical neighbourhood object and its maps have definitionally matching types; proof irrelevance ensures coherence.
  letI := isClosedImmersion_stageHomZero R m
  exact AlgebraicSpace.Hom.InfinitesimalNeighbourhood.space (stageHomZero R m) n

/-- The canonical map from stage zero to its neighbourhood inside stage `m`. -/
def neighbourhoodFromSource {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) (m n : ℕ) :
    infinitesimalStage R 0 ⟶ neighbourhoodSpace R m n := by
  -- Local instance justification (defeq pin): Pin the proof-class dictionary for this fixed stage immersion so the canonical neighbourhood object and its maps have definitionally matching types; proof irrelevance ensures coherence.
  letI := isClosedImmersion_stageHomZero R m
  exact AlgebraicSpace.Hom.InfinitesimalNeighbourhood.fromSource (stageHomZero R m) n

/-- The canonical map from a neighbourhood of stage zero to stage `m`. -/
def neighbourhoodToAmbient {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) (m n : ℕ) :
    neighbourhoodSpace R m n ⟶ infinitesimalStage R m := by
  -- Local instance justification (defeq pin): Pin the proof-class dictionary for this fixed stage immersion so the canonical neighbourhood object and its maps have definitionally matching types; proof irrelevance ensures coherence.
  letI := isClosedImmersion_stageHomZero R m
  exact AlgebraicSpace.Hom.InfinitesimalNeighbourhood.toAmbient (stageHomZero R m) n

/-- The comparison to the canonical neighbourhood retains each transition
section through the concrete coborder open-subspace lift. -/
def infinitesimalStageIsoNeighbourhood_hom {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage R n ⟶ neighbourhoodSpace R m n where
  app T := TypeCat.ofHom fun x ↦
    ⟨(AlgebraicSpace.OpenSubspace.Construction.lift
        (stageHom R hnm) (by sorry)).app T x, by sorry⟩
  naturality := sorry

/-- The inverse neighbourhood comparison sends a section to its ambient
section of the formal algebraic space. -/
def infinitesimalStageIsoNeighbourhood_inv {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    neighbourhoodSpace R m n ⟶ infinitesimalStage R n where
  app T := TypeCat.ofHom fun y ↦
    ⟨(stageι R m).app T ((neighbourhoodToAmbient R m n).app T y), by sorry⟩
  naturality := sorry

/-- Every earlier stage is canonically isomorphic to the corresponding
infinitesimal neighbourhood of stage zero in a later stage. -/
def infinitesimalStageIsoNeighbourhood {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    infinitesimalStage R n ≅ neighbourhoodSpace R m n where
  hom := infinitesimalStageIsoNeighbourhood_hom R hnm
  inv := infinitesimalStageIsoNeighbourhood_inv R hnm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The neighbourhood comparison commutes with the maps from the reduction. -/
theorem infinitesimalStageIsoNeighbourhood_fromSource
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    fromReduction R 0 ≫ neighbourhoodFromSource R m n =
      fromReduction R n ≫ (infinitesimalStageIsoNeighbourhood R hnm).hom :=
  sorry

/-- The neighbourhood comparison followed by its ambient map is the stage
transition. -/
theorem infinitesimalStageIsoNeighbourhood_toAmbient
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    (infinitesimalStageIsoNeighbourhood R hnm).hom ≫
        neighbourhoodToAmbient R m n = stageHom R hnm :=
  sorry

/-- The comparison from a presheaf colimit of the canonical stages is an
fppf-local isomorphism. -/
theorem eq_colimit_infinitesimalStages {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X)
    {c : Cocone (infinitesimalStages R ⋙ AlgebraicSpace.forgetToPresheaf)}
    (hc : IsColimit c) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (hc.desc (infinitesimalCocone R)) ∧
      Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
        (hc.desc (infinitesimalCocone R)) :=
  sorry

/-- Every canonical infinitesimal stage is locally Noetherian. -/
theorem isLocallyNoetherian_infinitesimalStage {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) (n : ℕ) :
    AlgebraicSpace.IsLocallyNoetherian (infinitesimalStage R n) :=
  sorry

/-- Every transition of canonical infinitesimal stages is a finite-order thickening. -/
theorem isFiniteOrderThickening_stageHom {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    AlgebraicSpace.IsFiniteOrderThickening (stageHom R hnm) :=
  sorry

/-- The canonical map from the reduction to stage zero is an isomorphism. -/
theorem infinitesimalStage_zero {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] (R : ReductionData X) :
    IsIso (fromReduction R 0) :=
  sorry

/-- The canonical neighbourhood comparison commutes with both the reduction
and the ambient transition. -/
theorem infinitesimalStageIsoNeighbourhood_spec {X : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X]
    (R : ReductionData X) {n m : ℕ} (hnm : n ≤ m) :
    fromReduction R 0 ≫ neighbourhoodFromSource R m n =
        fromReduction R n ≫ (infinitesimalStageIsoNeighbourhood R hnm).hom ∧
      (infinitesimalStageIsoNeighbourhood R hnm).hom ≫
        neighbourhoodToAmbient R m n = stageHom R hnm :=
  ⟨infinitesimalStageIsoNeighbourhood_fromSource R hnm,
    infinitesimalStageIsoNeighbourhood_toAmbient R hnm⟩

end AlgebraicGeometry.FormalAlgebraicSpace.ReductionData

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- A locally Noetherian formal algebraic space is the fppf-sheaf colimit of
the canonical finite-order thickenings of its reduction. Every stage is locally
Noetherian, stage zero is the reduction, and earlier stages are the canonical
infinitesimal neighbourhoods of stage zero inside later stages. -/
theorem exists_infinitesimalStages {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X] [IsLocallyNoetherian X] :
    ∃ (R : ReductionData X)
      (c : Cocone (R.infinitesimalStages ⋙ AlgebraicSpace.forgetToPresheaf))
      (hc : IsColimit c),
      (Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (hc.desc R.infinitesimalCocone) ∧
       Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
        (hc.desc R.infinitesimalCocone)) ∧
      (∀ n, AlgebraicSpace.IsLocallyNoetherian (R.infinitesimalStage n)) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m),
        AlgebraicSpace.IsFiniteOrderThickening (R.stageHom hnm)) ∧
      IsIso (R.fromReduction 0) ∧
      (∀ (n m : ℕ) (hnm : n ≤ m),
        R.fromReduction 0 ≫ R.neighbourhoodFromSource m n =
            R.fromReduction n ≫ (R.infinitesimalStageIsoNeighbourhood hnm).hom ∧
          (R.infinitesimalStageIsoNeighbourhood hnm).hom ≫
            R.neighbourhoodToAmbient m n = R.stageHom hnm) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
