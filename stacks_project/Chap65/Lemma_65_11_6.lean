/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleAtlasLift
import StacksCheckRecall

/-!
# Lifting surjective étale scheme atlases along morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

/- Lemma 65.11.6: let `S` be a scheme, and let `F`, `G` be algebraic spaces over `S`.
Let `a : F ⟶ G` be a morphism. Given a scheme `V` over `S` and a surjective étale
morphism `q : yoneda.obj V ⟶ G.functorOfPoints`, there exist a scheme `U` over `S`,
a morphism `α : U ⟶ V`, and a surjective étale morphism
`p : yoneda.obj U ⟶ F.functorOfPoints` making the square commute:
`p ≫ a = yoneda.map α ≫ q`. -/
@[stacks 02X1] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_etale_atlas_lift :
    ∀ {S : Scheme.{u}} {F G : AlgebraicSpace S} (a : F ⟶ G)
      {V : Over S} (q : yoneda.obj V ⟶ G.functorOfPoints)
      (hq_etale : (over (@Etale)).presheaf q)
      (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q),
      ∃ (U : Over S) (α : U ⟶ V) (p : yoneda.obj U ⟶ F.functorOfPoints),
        (over (@Etale)).presheaf p ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p ∧
            p ≫ a = yoneda.map α ≫ q)
