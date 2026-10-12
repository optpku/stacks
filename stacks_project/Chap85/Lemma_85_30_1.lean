/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Definition_85_27_1_Cartesian
public import stacks_project.Chap85.Lemma_85_30_1_Relation

/-!
# Lemma 85.30.1

A cartesian morphism of simplicial schemes over the Čech nerve of `f : X ⟶ S`
induces an equivalence relation on `Y _⦋0⦌` over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Simplicial
open Scheme.PreRelation

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable {Y : SimplicialObject Scheme.{u}} (π : Y ⟶ f.simplicialScheme)

/-- Lemma 85.30.1: if `π : Y ⟶ f.simplicialScheme` is a cartesian morphism of simplicial
schemes, then `j = (Y.δ 1, Y.δ 0) : Y _⦋1⦌ ⟶ Y _⦋0⦌ ×_S Y _⦋0⦌` defines an equivalence
relation on `Y _⦋0⦌` over `S`. -/
@[stacks 024E]
instance instIsEquivalenceRelation_facePreRelation [SimplicialObject.IsCartesian π] :
    IsEquivalenceRelation (facePreRelation f π).t (facePreRelation f π).s :=
  sorry

end AlgebraicGeometry.Scheme.Hom
