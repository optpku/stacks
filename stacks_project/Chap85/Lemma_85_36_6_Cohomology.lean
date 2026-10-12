/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap85.Lemma_85_33_2_Equivalence
public import stacks_project.Chap85.Lemma_85_33_4_Sections

/-!
# Spaces-étale cohomology, stage pullback, and first-page targets

Bounded-below étale cohomology of an abelian sheaf on an algebraic space is
`H^n_étale(Y, -)`, realized as homology of `RΓ(Y_étale, -)` after placing the
sheaf in `D⁺`. For an augmentation `a : U ⟶ X`, the source sheaf `F_n` is the
spaces-étale pullback of `F` along `a.app (op ⦋n⦌)`, and the first-page target
of the proper-hypercovering spectral sequence is `H^q_étale(U_p, F_p)`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace.Simplicial
open Functor DerivedCategory ZeroObject
open scoped Simplicial

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}}

/-- Spaces-étale cohomology `H^n_étale(Y, -)` of an abelian sheaf, as homology of
`RΓ(Y_étale, -)` after placing the sheaf in `D⁺` in degree `0`. -/
def plusCohomology (Y : AlgebraicSpace S) (n : ℤ) :
    Sheaf (spacesEtaleTopology Y) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Plus.singleFunctor _ 0 ⋙ plusGlobalSections Y ⋙ Plus.homologyFunctor AddCommGrpCat.{u + 1} n

/-- `plusCohomology Y n` is the composite of `Plus.singleFunctor` in degree `0` with
`plusGlobalSections Y` and `Plus.homologyFunctor` in degree `n`. -/
theorem plusCohomology_eq (Y : AlgebraicSpace S) (n : ℤ) :
    plusCohomology Y n =
      Plus.singleFunctor _ 0 ⋙
        plusGlobalSections Y ⋙ Plus.homologyFunctor AddCommGrpCat.{u + 1} n :=
  sorry

variable {X : AlgebraicSpace S} {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- The source sheaf `F_n` on `U_n,étale`: spaces-étale pullback of an abelian sheaf
on `X_étale` along the degree-`n` augmentation map `a.app (op ⦋n⦌)`. -/
def pullbackStage (n : ℕ) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
      Sheaf (spacesEtaleTopology (U.obj (op ⦋n⦌))) AddCommGrpCat.{u + 1} :=
  sheafPullbackConstruction.sheafPullback (spacesEtalePullback (a.app (op ⦋n⦌)))
    AddCommGrpCat.{u + 1} (spacesEtaleTopology X)
    (spacesEtaleTopology (U.obj (op ⦋n⦌)))

/-- `pullbackStage a n` is the Kan-extension sheaf pullback along
`spacesEtalePullback (a.app (op ⦋n⦌))`. -/
theorem pullbackStage_eq (n : ℕ) :
    pullbackStage a n =
      sheafPullbackConstruction.sheafPullback (spacesEtalePullback (a.app (op ⦋n⦌)))
        AddCommGrpCat.{u + 1} (spacesEtaleTopology X)
        (spacesEtaleTopology (U.obj (op ⦋n⦌))) :=
  sorry

/-- The stage pullback `F_n` is isomorphic to the degree-`n` component of the total
spaces-étale inverse image `a⁻¹ F`. -/
theorem pullbackStage_component (n : ℕ)
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) :
    IsIsomorphic ((pullbackStage a n).obj F)
      ((component U AddCommGrpCat.{u + 1} ⦋n⦌).obj
        ((inverseImage U AddCommGrpCat.{u + 1} a).obj F)) :=
  sorry

/-- Nonnegative first-page target: `H^q_étale(U_n, F_n)`. -/
def pageOneFunctorNonneg (n : ℕ) (q : ℤ) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  pullbackStage a n ⋙ plusCohomology (U.obj (op ⦋n⦌)) q

/-- First-page target `F ↦ H^q_étale(U_p, F_p)`, vanishing for `p < 0`. -/
def pageOneFunctor (p q : ℤ) :
    Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  if 0 ≤ p then pageOneFunctorNonneg a p.toNat q else
    (const (Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1})).obj
      (0 : AddCommGrpCat.{u + 1})

/-- Nonnegative bidegrees of `pageOneFunctor` recover `pageOneFunctorNonneg`. -/
theorem pageOneFunctor_eq_of_nonneg (p q : ℤ) (hp : 0 ≤ p) :
    pageOneFunctor a p q = pageOneFunctorNonneg a p.toNat q :=
  sorry

/-- First-page groups in negative Čech degree vanish. -/
theorem pageOneFunctor_neg
    (F : Sheaf (spacesEtaleTopology X) AddCommGrpCat.{u + 1}) {p : ℤ} (hp : p < 0)
    (q : ℤ) :
    IsZero ((pageOneFunctor a p q).obj F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
