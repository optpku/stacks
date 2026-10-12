/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap99.Situation_99_11_1
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion
public import stacks_project.Chap108.Lemma_108_9_4_GeometricFibres

/-!
# Lemma 108.9.4

If the geometric fibres of `f : X ⟶ B` are integral, in addition to the
standing hypotheses of Stacks 108.9, then the Picard functor `Pic_{X/B}` is
separated over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.9.4: assume the geometric fibres of `X ⟶ B` are integral in
addition to the standing hypotheses of this section (`f` flat, proper, of
finite presentation, and `O_T ⟶ f_{T,*} O_{X_T}` an isomorphism for every
scheme `T` over `B`). Then `Pic_{X/B} ⟶ B` is separated, i.e. the relative
diagonal of the Picard functor on `(Sch/B)` is a closed immersion. -/
@[stacks 0DNJ]
theorem separated (f : X ⟶ B) [Flat f] [Proper f] [FinitePresentation f]
    [Hom.IsIsoBaseChangeStructurePushforward f]
    [Hom.HasIntegralGeometricFibres f] :
    Quot.IsClosedImmersionOnSchemesOver (Limits.diag ((functor f).obj)) :=
  sorry

/-- The Picard functor `Pic_{X/B}` is separated over `B` if and only if the
relative diagonal of `picardFunctor f` is a closed immersion on schemes over
`B`. -/
theorem separated_iff (f : X ⟶ B) [Flat f] [Proper f] [FinitePresentation f]
    [Hom.IsIsoBaseChangeStructurePushforward f]
    [Hom.HasIntegralGeometricFibres f] :
    Quot.IsClosedImmersionOnSchemesOver (Limits.diag ((functor f).obj)) ↔
      Quot.IsClosedImmersionOnSchemesOver (Limits.diag ((picardFunctor f).obj)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
