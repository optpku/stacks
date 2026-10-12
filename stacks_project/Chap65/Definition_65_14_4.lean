/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_14_3_Relation
public import stacks_project.Chap65.Theorem_65_10_5
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PreRelation

universe u

/- Definition 65.14.4 (1): notation `U ⟶ S`, `G`, `R` as in Lemma 65.14.3.
If the action of `G` on `U` satisfies `(*)`, we say `G` acts freely on the
scheme `U`. This is the class `IsResidueFieldFree`. -/
@[stacks 02Z3] #check IsResidueFieldFree

/- Definition 65.14.4 (2): in this case the algebraic space `U/R` is denoted
`U/G` and is called the quotient of `U` by `G`, namely
`(ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)`. -/
@[stacks 02Z3] #check
  (fun {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
      (ρ : G →* Aut U) [IsResidueFieldFree ρ] =>
    (ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S))

@[stacks 02Z3] #check
  (fun {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
      (ρ : G →* Aut U) [IsResidueFieldFree ρ] =>
    quotientSheaf_spec (ofAut ρ))
