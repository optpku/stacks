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

/- Definition 65.14.4 (1): notation `U ⟶ S`, `G`, `R` as in Lemma 65.14.3.
If the action of `G` on `U` satisfies `(*)`, we say `G` acts freely on the
scheme `U`: every nonidentity group element fixing a point induces a
nonidentity automorphism of that point's residue field. -/
@[stacks 02Z3] #check
  (AlgebraicGeometry.Scheme.PreRelation.IsResidueFieldFree :
    ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G], (G →* Aut U) → Prop)

section

variable {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
  (ρ : G →* Aut U) [IsResidueFieldFree ρ]

/- Definition 65.14.4 (2): in this case the algebraic space `U/R` is denoted
`U/G` and is called the quotient of `U` by `G`, namely
`(ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)`. -/
@[stacks 02Z3] #check
  (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf
    (Scheme.fppfTopology.over S) (AlgebraicGeometry.Scheme.PreRelation.ofAut ρ) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))

end

/- Definition 65.14.4: for a free action, the quotient `U/G = U/R` has
representable diagonal, and its canonical quotient map is representable
étale and étale-locally surjective. -/
@[stacks 02Z3] #check
  (AlgebraicGeometry.Scheme.PreRelation.quotientSheaf_spec_ofAut :
    ∀ {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
      (ρ : G →* Aut U) [IsResidueFieldFree ρ],
      uliftYoneda.{u + 1}.relativelyRepresentable
          (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
        (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
          ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
          ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom)
