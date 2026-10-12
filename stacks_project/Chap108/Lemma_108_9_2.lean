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
public import stacks_project.Chap99.Situation_99_11_1
public import stacks_project.Chap108.Lemma_108_9_2_QuasiCompactImmersion

/-!
# Lemma 108.9.2

Under the standing hypotheses of Stacks 108.9, the relative diagonal of the
Picard functor `Pic_{X/B}` over `B` is a quasi-compact immersion.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.9.2: with assumptions and notation as in this section
(`f : X ⟶ B` flat, of finite presentation, and proper, and `O_T ⟶ f_{T,*} O_{X_T}`
an isomorphism for every scheme `T` over `B`), the relative diagonal of the
Picard functor `Pic_{X/B}` over `B` is a quasi-compact immersion. On `(Sch/B)`
this is the morphism `Limits.diag ((functor f).obj)`. -/
@[stacks 0DMF]
theorem isQuasiCompactImmersion_diagonal (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsQuasiCompactImmersionOnSchemesOver (Limits.diag ((functor f).obj)) :=
  sorry

/-- If the Picard functor is represented by a morphism `π : Y ⟶ B`, then `π` is
locally separated and quasi-separated. -/
theorem isQuasiCompactImmersion_diagonal_of_representable (f : X ⟶ B)
    [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] {Y : AlgebraicSpace S}
    {π : Y ⟶ B} (e : (functor f).obj ≅ yonedaOver π) :
    LocallySeparated π ∧ QuasiSeparated π :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
