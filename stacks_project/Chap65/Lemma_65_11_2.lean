/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.11.2: let `S` be a scheme contained in `Sch_fppf`. Let `G` be an
algebraic space over `S`, let `F` be a sheaf on `(Sch/S)_fppf`, and let
`G ⟶ F` be a representable transformation of functors which is surjective
and étale. Then `F` is an algebraic space. -/
@[stacks 0BGR] #check (AlgebraicGeometry.AlgebraicSpace.ofEtaleSurjectiveSpace_spec :
  ∀ {S : Scheme.{u}} {G : AlgebraicSpace S} {F : (Over S)ᵒᵖ ⥤ Type u},
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F →
    ∀ (a : G.functorOfPoints ⟶ F),
      (over (@Etale ⊓ @Surjective)).presheaf a →
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
          ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
            (over (@Etale)).presheaf p ∧
              Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
