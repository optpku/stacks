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

/- Lemma 65.14.3 (1): let `U ⟶ S` be a morphism of schemes, let `G` be an abstract
group, and let `ρ : G →* Aut U` be a homomorphism to automorphisms of `U` over `S`.
If a non-identity element fixing a point `u` of `U` induces a nontrivial
automorphism of `κ(u)`, then `j : R = ∐_G U ⟶ U ⨯ U`, `(g, x) ↦ (g(x), x)`, is
an étale equivalence relation. -/
@[stacks 02Z2] #check
  (@instIsEtaleEquivalenceRelation_ofAut :
    ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G] (ρ : G →* Aut U)
      [IsResidueFieldFree ρ], (ofAut ρ).IsEtaleEquivalenceRelation)

/- Lemma 65.14.3 (2): under the same hypotheses, the fppf quotient sheaf `U/R` of
`ofAut ρ` is an algebraic space by Theorem 65.10.5. -/
@[stacks 02Z2] #check
  (fun {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
      (ρ : G →* Aut U) [IsResidueFieldFree ρ] =>
    quotientSheaf_spec (ofAut ρ))
