/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.«98_5_3_1_Comparison»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Displayed restriction comparison of fibrewise 2-fibre products

After identifying fibres of a 2-fibre product of categories fibred in groupoids
with 2-fibre products of fibres, restriction along a commuting square of schemes
over `S` is the nested comparison functor of fibrewise 2-fibre products.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits CategoricalPullback
open FiberedCategoryOver.Groupoids
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}
variable {𝒳 𝒴 𝒵 : GroupoidsOver S}

/-- 98.5.3.1: for 1-morphisms `p : 𝒳 ⟶ 𝒴` and `q : 𝒵 ⟶ 𝒴` of categories fibred in
groupoids over `(Sch/S)_fppf`, and a commuting square of schemes over `S`, restriction
of fibrewise 2-fibre products is the functor
`𝒳_{Y'} ×_{𝒴_{Y'}} 𝒵_{Y'} ⟶
(𝒳_Y ×_{𝒴_Y} 𝒵_Y) ×_{(𝒳_X ×_{𝒴_X} 𝒵_X)} (𝒳_{X'} ×_{𝒴_{X'}} 𝒵_{X'})`,
namely
`(fiberFunctor p Y') ⊡ (fiberFunctor q Y') ⥤
(fibreProductReindex p q toY) ⊡ (fibreProductReindex p q toX')`. -/
@[stacks 07WS]
noncomputable def fibreProductRestrictionComparison
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : Over S} {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY) :
    (fiberFunctor p Y') ⊡ (fiberFunctor q Y') ⥤
      (fibreProductReindex p q toY) ⊡ (fibreProductReindex p q toX') :=
  FiberedCategoryOver.Groupoids.fibreProductRestrictionComparison p q hw

/-- Objects of the displayed comparison record the two fibrewise 2-fibre-product
reindexings and the structural 2-cell. -/
theorem fibreProductRestrictionComparison_spec
    (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)
    {X X' Y Y' : Over S} {toX' : X ⟶ X'} {toY : X ⟶ Y}
    {fromX' : X' ⟶ Y'} {fromY : Y ⟶ Y'}
    (hw : toX' ≫ fromX' = toY ≫ fromY)
    (t : (fiberFunctor p Y') ⊡ (fiberFunctor q Y')) :
    ((fibreProductRestrictionComparison p q hw).obj t).fst =
      (fibreProductReindex p q fromY).obj t ∧
      ((fibreProductRestrictionComparison p q hw).obj t).snd =
        (fibreProductReindex p q fromX').obj t ∧
      ((fibreProductRestrictionComparison p q hw).obj t).iso =
        (fibreProductRestrictionSquare p q hw).iso.app t := sorry

end AlgebraicGeometry.GroupoidsOver
