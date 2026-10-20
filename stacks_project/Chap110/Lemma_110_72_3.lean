/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cohomology
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/-!
# Fppf H¹ of a smooth commutative group algebraic space over a field is torsion
-/

/- Lemma 110.72.3 -/
@[stacks 0AFA] #check
  (AlgebraicGeometry.fppfH1_isTorsion_of_smoothAtlas :
    ∀ {K : Type u} [Field K]
      (G : Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) AddCommGrpCat.{u})
      [HasSheafify (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) AddCommGrpCat.{u}]
      [HasExt.{u} (Sheaf (Scheme.fppfTopology.over (Spec (CommRingCat.of K))) AddCommGrpCat.{u})]
      (h_diagonal : yoneda.relativelyRepresentable
        (Limits.diag (G.obj ⋙ forget AddCommGrpCat.{u})))
      (h_atlas : ∃ (U : Over (Spec (CommRingCat.of K)))
        (atlas : yoneda.obj U ⟶ G.obj ⋙ forget AddCommGrpCat.{u}),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf atlas ∧
          Presheaf.IsLocallySurjective
            (Scheme.etaleTopology.over (Spec (CommRingCat.of K))) atlas ∧
            AlgebraicGeometry.Smooth U.hom),
      AddMonoid.IsTorsion (G.H 1))
