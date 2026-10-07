module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap110.Lemma_110_52_1_Comparison
public import stacks_project.Chap110.Lemma_110_52_1_Principal
public import stacks_project.Chap110.Lemma_110_52_1_Torsors

/-!
# Non-equivalence of principal homogeneous spaces and fppf torsors
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open AlgebraicGeometry.GroupAlgebraicSpace
open StackOver.Groupoids.Hom
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Lemma 110.52.1: there exist a scheme `S` and a group scheme `G` over `S`
such that the stack `Principal.stack (toGroupAlgebraicSpace G)` of principal
homogeneous `G`-spaces (Examples of Stacks 95.14.5) and the stack
`Torsors.stack (toGroupAlgebraicSpace G)` of fppf `G`-torsors (Examples of
Stacks 95.14.8) are not equivalent over `(Sch/S)_fppf`. -/
@[stacks 077B]
theorem exists_principal_notEquivalent_fppfTorsors :
    ∃ (S : Scheme.{u}) (G : GroupScheme S),
      ¬ BasedFunctor.IsEquivalence (toBasedFunctor (toPrincipal G)) := sorry

end AlgebraicGeometry.GroupScheme
