/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OfRepresentable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {G : (Over S)ᵒᵖ ⥤ Type u}
/- Lemma 65.11.3: let `S` be a scheme contained in `Sch_fppf`. Let `F` be an algebraic
space over `S`. Let `G ⟶ F` be a representable transformation of functors. Then `G`
is an algebraic space. -/
@[stacks 02WY] #check
  (AlgebraicGeometry.AlgebraicSpace.ofRelativelyRepresentable_spec :
    ∀ {S : Scheme.{u}} {F : AlgebraicSpace S} {G : (Over S)ᵒᵖ ⥤ Type u},
      (a : G ⟶ F.functorOfPoints) →
        (ha : yoneda.relativelyRepresentable a) →
          Presheaf.IsSheaf (Scheme.fppfTopology.over S) G ∧
            yoneda.relativelyRepresentable (Limits.diag G) ∧
              ∃ (U : Over S) (p : yoneda.obj U ⟶ G),
                MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
                  Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
