/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 66.34.1: if `S` is a scheme, `X` is an algebraic space over `S`, and an
abstract group `G` acts freely on `X` via `ρ : G →* Aut X`, then the fppf sheaf
associated to `T ↦ X(T)/G` is an algebraic space. -/
@[stacks 071S]
#check (AlgebraicGeometry.AlgebraicSpace.quotientSheaf_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {G : Type u} [Group G]
    (ρ : G →* Aut X) [AlgebraicSpace.IsFree ρ],
    uliftYoneda.{u + 1}.relativelyRepresentable
        (diag (AlgebraicSpace.quotientSheaf ρ).obj) ∧
      ∃ (U : Over S)
        (p : (Scheme.fppfTopology.over S).uliftYoneda.{u + 1}.obj U ⟶
          AlgebraicSpace.quotientSheaf ρ),
        (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} p.hom ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p.hom)
