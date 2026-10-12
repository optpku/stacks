/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap101.Lemma_101_25_5_Surjective
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap106.Lemma_106_10_1_ZariskiLocal

/-!
# Finite covers factoring Zariski locally through a stack morphism

A quasi-compact quasi-separated algebraic space admits, after a finite
surjective base change, a Zariski-local factoring of the inverse image of a
quasi-compact open through any surjective flat locally-of-finite-presentation
morphism of algebraic stacks onto that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 106.10.1. Let `Y` be a quasi-compact and quasi-separated algebraic
space. Let `V ⊂ Y` be a quasi-compact open. Let `f : X ⟶ V` be surjective,
flat, and locally of finite presentation. Then there exists a finite surjective
morphism `g : Y' ⟶ Y` such that `V' = g⁻¹(V) ⟶ Y` factors Zariski locally
through `f`. Here `V'` is `openInverseImage g V.ι` and the comparison
`V' ⟶ V` is `openInverseImageTo g V.ι`. -/
@[stacks 0CQ6]
theorem exists_isFinite_surjective_zariskiLocallyFactorsThrough
    {S : Scheme.{u}} (Y : AlgebraicSpace S)
    [AlgebraicSpace.IsQuasiCompact Y]
    [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
    (V : AlgebraicSpace.OpenSubspace Y) [AlgebraicSpace.IsQuasiCompact V.X]
    {X : GroupoidsOver S} [AlgebraicStack X] (f : X ⟶ V.X.toGroupoids)
    [AlgebraicStack.Surjective f] [AlgebraicStack.Flat f]
    [AlgebraicStack.LocallyOfFinitePresentation f] :
    ∃ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
      AlgebraicSpace.IsFinite g ∧ AlgebraicSpace.Surjective g ∧
        zariskiLocallyFactorsThrough (AlgebraicSpace.openInverseImageTo g V.ι) f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
