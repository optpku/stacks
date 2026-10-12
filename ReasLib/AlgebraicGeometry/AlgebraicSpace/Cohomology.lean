/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.GroupTheory.Torsion

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

noncomputable section

/-- The first fppf cohomology group of a smooth commutative group algebraic space over a field is
torsion. -/
theorem fppfH1_isTorsion_of_smoothAtlas {K : Type u} [Field K]
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
          AlgebraicGeometry.Smooth U.hom) :
    AddMonoid.IsTorsion (G.H 1) := sorry

end

end AlgebraicGeometry
