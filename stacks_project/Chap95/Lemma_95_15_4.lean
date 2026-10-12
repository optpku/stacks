/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap78.Lemma_78_27_2_TrivialAction
public import stacks_project.Chap95.Lemma_95_14_10
public import stacks_project.Chap95.Proposition_95_15_3
public import stacks_project.Chap110.Lemma_110_52_1_Comparison

/-!
# Lemma 95.15.4

The classifying stacks `[B/G]`, `[[B/G]]`, `G`-Torsors, and `𝒢/ℬ`-Torsors
are canonically equivalent over `(Sch/S)_fppf`. If `G ⟶ B` is flat and
locally of finite presentation, they are also equivalent to `G`-Principal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupAlgebraicSpace
open AlgebraicGeometry.QuotientStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Classifying

/- Lemma 95.15.4 (1): the stacks `[B/G]` and `[[B/G]]` are canonically equivalent
over `(Sch/S)_fppf`, via `GroupAction.equivalent G (trivialAction G)`. -/
@[stacks 0CQJ] #check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) ↦
    GroupAction.equivalent_isEquivalence G (trivialAction G)

/-- Lemma 95.15.4 (2): the stacks `[[B/G]]` and `G`-Torsors are canonically
equivalent over `(Sch/S)_fppf`, via `GroupAction.toTorsors G (trivialAction G)`. -/
@[stacks 0CQJ, instance]
instance toTorsors_trivialAction_isEquivalence {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (GroupAction.toTorsors G (trivialAction G)).toBasedFunctor.IsEquivalence := sorry

/- Lemma 95.15.4 (3): the stacks `G`-Torsors and `𝒢/ℬ`-Torsors are canonically
equivalent over `(Sch/S)_fppf`, via `toSheafHom G`. -/
@[stacks 0CQJ] #check
  fun {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) ↦
    toSheafHom_isEquivalence G

/-- Lemma 95.15.4 (4): if `G ⟶ B` is flat and locally of finite presentation,
then `G`-Torsors is canonically equivalent to `G`-Principal over `(Sch/S)_fppf`,
via `toPrincipal G`. -/
@[stacks 0CQJ, instance]
instance toPrincipal_isEquivalence {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) [AlgebraicSpace.Flat G.X.hom]
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    IsEquivalence (toPrincipal G) := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Classifying
