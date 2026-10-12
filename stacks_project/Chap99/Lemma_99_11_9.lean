/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_3_8_Yoneda
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap99.Lemma_99_11_9_Immersion
public import stacks_project.Chap99.Situation_99_11_1

/-!
# Lemma 99.11.9

Under the standing hypotheses of Proposition 99.11.8, the diagonal of the
Picard functor `Pic_{X/B}` is representable by immersions, equivalently
`Pic_{X/B} ⟶ B` is locally separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.9: with assumptions and notation as in Proposition 99.11.8
(`f : X ⟶ B` flat, of finite presentation, and proper, and `O_T ⟶ f_{T,*} O_{X_T}`
an isomorphism for every scheme `T` over `B`), the diagonal
`Pic_{X/B} ⟶ Pic_{X/B} ×_B Pic_{X/B}` is representable by immersions. In other
words, `Pic_{X/B} ⟶ B` is locally separated. -/
@[stacks 0D2D]
theorem locallySeparated (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsImmersionOnSchemesOver (Limits.diag ((functor f).obj)) :=
  sorry

/-- If the Picard functor is represented by a morphism `π : Y ⟶ B`, then `π` is
locally separated. -/
theorem locallySeparated_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (functor f).obj ≅ yonedaOver π) :
    LocallySeparated π :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
