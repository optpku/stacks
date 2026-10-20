/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.GroupAction
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.QuotientSheaf.Presentation

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- The fppf quotient of a residue-field free group action has representable diagonal,
and its canonical atlas is representable étale and étale-locally surjective. -/
theorem quotientSheaf_spec_ofAut {S : Scheme.{u}} {U : Over S} {G : Type u} [Group G]
    (ρ : G →* Aut U) [IsResidueFieldFree ρ] :
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag ((ofAut ρ).quotientSheaf (Scheme.fppfTopology.over S)).obj) ∧
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1}
        ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        ((ofAut ρ).quotientMap (Scheme.fppfTopology.over S)).hom :=
  quotientSheaf_spec (ofAut ρ)

end AlgebraicGeometry.Scheme.PreRelation
