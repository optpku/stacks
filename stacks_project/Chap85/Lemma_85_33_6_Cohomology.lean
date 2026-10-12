/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import stacks_project.Chap85.Lemma_85_33_3_Adjunction
public import stacks_project.Chap85.Lemma_85_33_4_Sections

/-!
# Stage pullbacks and spaces-étale cohomology

Pullback of an abelian sheaf on `X_étale` to a simplicial stage `U_n,étale`, and
the cohomology functor `H^q_étale(Y, -)` obtained from bounded-below derived
global sections on `spacesEtaleTopology Y`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Functor
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- The degree-`n` map `U_n ⟶ X` of an augmentation `a : U ⟶ X`. -/
def augmentationApp {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    U.obj (op ⦋n⦌) ⟶ X :=
  a.app (op ⦋n⦌)

/-- `augmentationApp a n` is the component of `a` at `op ⦋n⦌`. -/
theorem augmentationApp_eq {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    augmentationApp a n = a.app (op ⦋n⦌) :=
  sorry

/-- Inverse image of an abelian sheaf on `X_étale` along the degree-`n` map of an
augmentation `a : U ⟶ X`, landing on `U_n,étale`. This is the sheaf `F_n` of
the fppf-hypercovering spectral sequence. -/
def stageInverseImage {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (spacesEtaleTopology (U.obj (op ⦋n⦌))) AddCommGrpCat.{u + 1} :=
  (spacesEtalePullback (augmentationApp a n)).sheafPullback AddCommGrpCat.{u + 1}
    (spacesEtaleTopology X) (spacesEtaleTopology (U.obj (op ⦋n⦌)))

/-- `stageInverseImage a n` is sheaf pullback along `spacesEtalePullback` of
`augmentationApp a n`. -/
theorem stageInverseImage_eq {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    stageInverseImage a n =
      (spacesEtalePullback (augmentationApp a n)).sheafPullback AddCommGrpCat.{u + 1}
        (spacesEtaleTopology X) (spacesEtaleTopology (U.obj (op ⦋n⦌))) :=
  sorry

/-- Evaluating `stageInverseImage a n` on `F` is sheaf pullback of `F` along the degree-`n`
augmentation map. -/
theorem stageInverseImage_obj {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (stageInverseImage a n).obj F =
      ((spacesEtalePullback (augmentationApp a n)).sheafPullback AddCommGrpCat.{u + 1}
        (spacesEtaleTopology X) (spacesEtaleTopology (U.obj (op ⦋n⦌)))).obj F :=
  sorry

/-- The functor sending an abelian sheaf on `Y_étale` to its spaces-étale cohomology
`H^q_étale(Y, -)`, as homology of `RΓ(Y_étale, G[0])`. -/
def spacesEtaleCohomologyFunctor (Y : AlgebraicSpace S) (q : ℕ) :
    Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor
      (Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}) 0 ⋙
    plusGlobalSections Y ⋙
    DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q

/-- Spaces-étale cohomology `H^q_étale(Y, G)` of an abelian sheaf. -/
abbrev spacesEtaleCohomology (Y : AlgebraicSpace S)
    (G : Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  (spacesEtaleCohomologyFunctor Y q).obj G

/-- Evaluating the spaces-étale cohomology functor is homology of derived global sections of
the complex concentrated in degree zero. -/
theorem spacesEtaleCohomologyFunctor_obj (Y : AlgebraicSpace S)
    (G : Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    (spacesEtaleCohomologyFunctor Y q).obj G =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u + 1} q).obj
        ((plusGlobalSections Y).obj
          ((DerivedCategory.Plus.singleFunctor
              (Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}) 0).obj G)) :=
  sorry

/-- `spacesEtaleCohomology Y G q` is the value of `spacesEtaleCohomologyFunctor Y q` on `G`. -/
theorem spacesEtaleCohomology_eq (Y : AlgebraicSpace S)
    (G : Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}) (q : ℕ) :
    spacesEtaleCohomology Y G q = (spacesEtaleCohomologyFunctor Y q).obj G :=
  sorry

/-- Stage pullback `F_n` is isomorphic to the degree-`n` component of the total-site
inverse image `a⁻¹ F`. -/
theorem stageInverseImage_component {X : AlgebraicSpace S}
    {U : SimplicialObject (AlgebraicSpace S)}
    (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X) (n : ℕ)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    Nonempty
      ((stageInverseImage a n).obj F ≅
        (component U AddCommGrpCat.{u + 1} ⦋n⦌).obj
          ((inverseImage U AddCommGrpCat.{u + 1} a).obj F)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
