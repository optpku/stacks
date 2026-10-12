/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_4_8_Opens

/-!
# Open subspaces cut out by opens of points

An open of `Points X` determines an open subspace of an algebraic space `X` as
the subfunctor of maps into `X` whose image of points lands in that open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.OpenSubspace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The morphism `ofOver U.unop ⟶ X` associated to a section of the functor of points. -/
def homOfPointsSection {U : (Over S)ᵒᵖ} (φ : X.functorOfPoints.obj U) :
    ofOver U.unop ⟶ X :=
  yonedaEquiv.symm φ

/-- `homOfPointsSection φ` is the Yoneda transpose of a section of the functor of points. -/
theorem homOfPointsSection_eq {U : (Over S)ᵒᵖ} (φ : X.functorOfPoints.obj U) :
    homOfPointsSection φ = yonedaEquiv.symm φ :=
  sorry

/-- The subfunctor of maps into `X` whose image of points lands in `W`. -/
def ofOpensSubfunctor (W : Opens (Points X)) : Subfunctor X.functorOfPoints where
  obj U := {φ | Set.range (Points.map (homOfPointsSection φ)) ⊆ W}
  map := sorry

/-- The algebraic space underlying the open subspace cut out by `W`. -/
def ofOpensSpace (W : Opens (Points X)) : AlgebraicSpace S :=
  ofFunctor (ofOpensSubfunctor W).toFunctor sorry sorry sorry

/-- The inclusion of the open subspace cut out by `W` into `X`. -/
def ofOpensι (W : Opens (Points X)) : ofOpensSpace W ⟶ X :=
  (ofOpensSubfunctor W).ι

/-- The inclusion of the open subspace cut out by `W` is an open immersion. -/
instance instIsOpenImmersion_ofOpensι (W : Opens (Points X)) :
    IsOpenImmersion (ofOpensι W) :=
  sorry

/-- The open subspace of `X` with underlying point-set `W`. -/
def ofOpens (W : Opens (Points X)) : OpenSubspace X :=
  ofι (ofOpensι W)

/-- The inclusion of `ofOpens W` is an open immersion. -/
instance instIsOpenImmersion_ofOpens_ι (W : Opens (Points X)) :
    IsOpenImmersion (ofOpens W).ι :=
  (ofOpens W).isOpenImmersion

/-- The functor of points of `ofOpensSpace W` is the points-cut subfunctor. -/
theorem ofOpensSpace_functorOfPoints (W : Opens (Points X)) :
    (ofOpensSpace W).functorOfPoints = (ofOpensSubfunctor W).toFunctor :=
  sorry

/-- The inclusion `ofOpensι W` is the subfunctor inclusion. -/
theorem ofOpensι_eq (W : Opens (Points X)) :
    ofOpensι W = (ofOpensSubfunctor W).ι :=
  sorry

/-- The underlying point-set of `ofOpens W` is `W`. -/
theorem ofOpens_pointsSet (W : Opens (Points X)) :
    (ofOpens W).pointsSet = W :=
  sorry

/-- The open subspace `ofOpens W` occupies the open `W`, and is unique up to unique
lift over `X`. -/
theorem ofOpens_spec (W : Opens (Points X)) :
    (ofOpens W).pointsSet = W ∧
      ∀ V : OpenSubspace X, V.pointsSet = W →
        ∃! f : V.X ⟶ (ofOpens W).X, f ≫ (ofOpens W).ι = V.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.OpenSubspace
