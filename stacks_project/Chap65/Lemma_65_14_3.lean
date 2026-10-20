/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.GroupAction
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PreRelation

universe u

/- Lemma 65.14.3 (1): let `U ⟶ S` be a morphism of schemes, let `G` be an abstract
group, and let `ρ : G →* Aut U` be a homomorphism to automorphisms of `U` over `S`.
If a non-identity element fixing a point `u` of `U` induces a nontrivial
automorphism of `κ(u)`, then `j : R = ∐_G U ⟶ U ⨯ U`, `(g, x) ↦ (g(x), x)`, is
an étale equivalence relation. -/
@[stacks 02Z2] #check
  (AlgebraicGeometry.Scheme.PreRelation.instIsEtaleEquivalenceRelation_ofAut :
    ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G] (ρ : G →* Aut U)
      [IsResidueFieldFree ρ], (ofAut ρ).IsEtaleEquivalenceRelation)

/- Lemma 65.14.3 (2): under the same hypotheses, the fppf quotient sheaf `U/R` of
`ofAut ρ` is an algebraic space by Theorem 65.10.5. -/
@[stacks 02Z2] #check
  (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_spec_ofAut :
    ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G] (ρ : G →* Aut U)
      [IsResidueFieldFree ρ],
      uliftYoneda.{u + 1}.relativelyRepresentable
          (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
        (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
          ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
          ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom)
