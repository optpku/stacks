/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import stacks_project.Chap75.Lemma_75_20_4_BaseChange

/-!
# Derived pullback 2-fibre products along commutative squares

A commutative square of algebraic spaces, together with invertibility of the two
derived-pullback composition comparisons, induces a functor
`D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` whose components are derived
pullbacks.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoricalPullback
open scoped CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
variable [IsIso (modulePullbackDerived.compComparison f j)]
variable [IsIso (modulePullbackDerived.compComparison i f')]

/-- The derived pullback identification of the two paths around a commutative square of
algebraic spaces, obtained from invertibility of the composition comparisons and the
square equality `i ≫ f' = f ≫ j`. -/
def modulePullbackDerived.pushoutSquareIso (sq : CommSq i f f' j) :
    modulePullbackDerived j ⋙ modulePullbackDerived f ≅
      modulePullbackDerived f' ⋙ modulePullbackDerived i :=
  asIso (modulePullbackDerived.compComparison f j) ≪≫
    eqToIso (congrArg (fun p : X ⟶ Y' ↦ modulePullbackDerived p) sq.w.symm) ≪≫
    (asIso (modulePullbackDerived.compComparison i f')).symm

/-- The forward morphism of `modulePullbackDerived.pushoutSquareIso` is the composition
comparison along `f ≫ j`, transport along `sq.w`, and the inverse comparison along
`i ≫ f'`. -/
theorem modulePullbackDerived.pushoutSquareIso_hom (sq : CommSq i f f' j) :
    (modulePullbackDerived.pushoutSquareIso sq).hom =
      modulePullbackDerived.compComparison f j ≫
        eqToHom (congrArg (fun p : X ⟶ Y' ↦ modulePullbackDerived p) sq.w.symm) ≫
          inv (modulePullbackDerived.compComparison i f') :=
  sorry

/-- The commutative square of derived pullbacks associated to a commutative square of
algebraic spaces. -/
def modulePullbackDerived.pushoutSquare (sq : CommSq i f f' j) :
    CatCommSqOver (modulePullbackDerived f) (modulePullbackDerived i)
      (ModuleDerived Y') where
  fst := modulePullbackDerived j
  snd := modulePullbackDerived f'
  iso := modulePullbackDerived.pushoutSquareIso sq

/-- The functor `D(𝒪_{Y'}) ⥤ D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` given by derived pullback
along the two legs of a commutative square of algebraic spaces. -/
def modulePullbackDerived.pushoutSquareFunctor (sq : CommSq i f f' j) :
    ModuleDerived Y' ⥤ (modulePullbackDerived f) ⊡ (modulePullbackDerived i) :=
  (modulePullbackDerived.pushoutSquare sq).comparison

/-- The first projection of `modulePullbackDerived.pushoutSquareFunctor` recovers derived
pullback along `j`. -/
theorem modulePullbackDerived.pushoutSquareFunctor_obj_fst (sq : CommSq i f f' j)
    (M' : ModuleDerived Y') :
    ((modulePullbackDerived.pushoutSquareFunctor sq).obj M').fst =
      (modulePullbackDerived j).obj M' :=
  sorry

/-- The second projection of `modulePullbackDerived.pushoutSquareFunctor` recovers derived
pullback along `f'`. -/
theorem modulePullbackDerived.pushoutSquareFunctor_obj_snd (sq : CommSq i f f' j)
    (M' : ModuleDerived Y') :
    ((modulePullbackDerived.pushoutSquareFunctor sq).obj M').snd =
      (modulePullbackDerived f').obj M' :=
  sorry

/-- The structural isomorphism of `modulePullbackDerived.pushoutSquareFunctor` is the
component of `modulePullbackDerived.pushoutSquareIso`. -/
theorem modulePullbackDerived.pushoutSquareFunctor_obj_iso (sq : CommSq i f f' j)
    (M' : ModuleDerived Y') :
    ((modulePullbackDerived.pushoutSquareFunctor sq).obj M').iso =
      (modulePullbackDerived.pushoutSquareIso sq).app M' :=
  sorry

/-- Source-facing constructor for a triple in `D(𝒪_Y) ×_{D(𝒪_X)} D(𝒪_{X'})` from
objects `M`, `K'` and an identification `Lf^* M ≅ Li^* K'`. -/
def modulePullbackDerived.pullbackTriple
    (M : ModuleDerived Y) (K' : ModuleDerived X')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived f) ⊡ (modulePullbackDerived i) where
  fst := M
  snd := K'
  iso := α

/-- The first component of `modulePullbackDerived.pullbackTriple` is the object of
`D(𝒪_Y)`. -/
theorem modulePullbackDerived.pullbackTriple_fst
    (M : ModuleDerived Y) (K' : ModuleDerived X')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived.pullbackTriple M K' α).fst = M :=
  sorry

/-- The second component of `modulePullbackDerived.pullbackTriple` is the object of
`D(𝒪_{X'})`. -/
theorem modulePullbackDerived.pullbackTriple_snd
    (M : ModuleDerived Y) (K' : ModuleDerived X')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived.pullbackTriple M K' α).snd = K' :=
  sorry

/-- The structural isomorphism of `modulePullbackDerived.pullbackTriple` is the given
identification `Lf^* M ≅ Li^* K'`. -/
theorem modulePullbackDerived.pullbackTriple_iso
    (M : ModuleDerived Y) (K' : ModuleDerived X')
    (α : (modulePullbackDerived f).obj M ≅ (modulePullbackDerived i).obj K') :
    (modulePullbackDerived.pullbackTriple M K' α).iso = α :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
