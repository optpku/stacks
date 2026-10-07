module

public import stacks_project.Chap70.«70_4_1_1_Comparison»
public import stacks_project.Chap87.Lemma_87_20_11_InfinitesimalStages

/-!
# Lemma 87.20.11

A locally Noetherian formal algebraic space is the fppf-sheaf colimit of the
canonical system of infinitesimal neighbourhoods of its reduction.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicSpace.Hom.InfinitesimalNeighbourhood

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.20.11 (1): Let `S` be a scheme and let `X` be a locally Noetherian
formal algebraic space over `S`. Then `X` is the colimit of the canonical
system of infinitesimal stages as fppf sheaves: the comparison from any
presheaf colimit of `infinitesimalStages X ⋙ AlgebraicSpace.forgetToPresheaf`
to `X` is an fppf-local isomorphism.

Lean indexes the system by `ℕ` with object `n` cut out by `I^{n+1} = 0`, so
Stacks `X_1 = X_red` is `infinitesimalStage X 0` and Stacks `X_{n+1}` is Lean
object `n`. The reduction is the ambient data `[Reduction X]`.
-/
@[stacks 0GHM]
theorem eq_colimit_infinitesimalStages {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X]
    {c : Cocone (infinitesimalStages X ⋙ AlgebraicSpace.forgetToPresheaf)}
    (hc : IsColimit c) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (hc.desc (infinitesimalCocone X)) ∧
      Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
        (hc.desc (infinitesimalCocone X)) :=
  sorry

/-- Lemma 87.20.11 (2): each infinitesimal stage of a locally Noetherian formal
algebraic space is a locally Noetherian algebraic space. Lean object `n` is
Stacks `X_{n+1}`, with Stacks `X_1 = X_red` as `infinitesimalStage X 0`.
-/
@[stacks 0GHM, instance]
instance instIsLocallyNoetherian_infinitesimalStage {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] (n : ℕ) :
    AlgebraicSpace.IsLocallyNoetherian (infinitesimalStage X n) :=
  sorry

/-- Lemma 87.20.11 (3): the transition morphisms of the infinitesimal-stage
system are finite-order thickenings of locally Noetherian algebraic spaces.
Lean object `n` is Stacks `X_{n+1}`.
-/
@[stacks 0GHM, instance]
instance instIsFiniteOrderThickening_stageHom {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    AlgebraicSpace.IsFiniteOrderThickening (stageHom X hnm) :=
  sorry

/-- Lemma 87.20.11 (4): Stacks `X_1 = X_red`. The canonical map from the
reduction to Lean object `0` is an isomorphism of algebraic spaces.
-/
@[stacks 0GHM, instance]
instance infinitesimalStage_zero {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] :
    IsIso (fromReduction X 0) :=
  sorry

/-- Lemma 87.20.11 (5): for `n ≤ m`, Lean object `n` is the `n`th infinitesimal
neighbourhood of object `0` inside object `m`. Stacks `X_1` is
`infinitesimalStage X 0` and Stacks `X_{n+1}` is Lean object `n`.
-/
@[stacks 0GHM]
theorem infinitesimalStageIsoNeighbourhood_spec {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsFormalAlgebraicSpace X]
    [IsLocallyNoetherian X] [Reduction X] {n m : ℕ} (hnm : n ≤ m) :
    fromReduction X 0 ≫ fromSource (stageHomZero X m) n =
      fromReduction X n ≫ (infinitesimalStageIsoNeighbourhood X hnm).hom ∧
    (infinitesimalStageIsoNeighbourhood X hnm).hom ≫
        toAmbient (stageHomZero X m) n =
      stageHom X hnm :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
