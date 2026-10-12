/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Unbounded.LeftDerived.Bounds
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap70.Lemma_70_14_4_Pullback
public import stacks_project.Chap75.Lemma_75_21_2
public import stacks_project.Chap75.Lemma_75_26_4_VectorBundle
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# First higher direct image of the structure sheaf

The sheaf `R^1 f_* 𝒪_X` on an algebraic space is the degree-one cohomology of
the derived pushforward of `𝒪_X`. Its formation along an arbitrary morphism of
the base is compared by a canonical module morphism assembled from lower
truncation, derived base change, and the structure-sheaf pullback identification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Derived pullback of module sheaves is a left derived functor of underived
module pullback. -/
instance instIsLeftDerivedFunctor_pullback {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) :
    (pullback g).IsLeftDerivedFunctor
      (Functor.LeftDerived.Homotopy.counit (Modules.pullback g))
      (HomotopyCategory.quasiIso (Modules X) (ComplexShape.up ℤ)) :=
  Functor.LeftDerived.Homotopy.isLeftDerived (Modules.pullback g)

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/-- The first higher direct image `R^1 f_* 𝒪_X` of the structure sheaf, as the
degree-one cohomology sheaf of `Rf_* 𝒪_X`. -/
abbrev higherDirectImageOne {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.Modules :=
  ModuleDerived.cohomologySheaf
    ((Modules.pushforwardDerived f).obj
      ((DerivedCategory.singleFunctor (Modules X) 0).obj
        (SheafOfModules.unit (structureSheaf X)))) 1

/-- `higherDirectImageOne f` is the degree-one cohomology sheaf of `Rf_* 𝒪_X`. -/
theorem higherDirectImageOne_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    higherDirectImageOne f =
      ModuleDerived.cohomologySheaf
        ((Modules.pushforwardDerived f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj
            (SheafOfModules.unit (structureSheaf X)))) 1 :=
  sorry

/-- The canonical comparison `g^* (R^1 f_* 𝒪_X) ⟶ R^1 f'_* 𝒪_{X'}` associated to
an arbitrary base change of `f` along `g`. -/
def higherDirectImageOneBaseChangeHom {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y' ⟶ Y) :
    (Modules.pullback g).obj (higherDirectImageOne f) ⟶
      higherDirectImageOne (pullback.snd f g) :=
  let OX := (DerivedCategory.singleFunctor (Modules X) 0).obj
    (SheafOfModules.unit (structureSheaf X))
  let E := (Modules.pushforwardDerived f).obj OX
  (Modules.pullback g).map
      ((DerivedCategory.homologyFunctor (Modules Y) 1).map ((t.truncGEπ 1).app E)) ≫
    ModuleDerived.cohomologyPullbackComparison g ((t.truncGE 1).obj E) 1
      inferInstance inferInstance ≫
    (Functor.LeftDerived.Homotopy.TruncGE.homologyIso (Modules.pullback g)
        (ModuleDerived.pullback g) (Functor.LeftDerived.Homotopy.counit (Modules.pullback g))
        E 1 1 le_rfl).inv ≫
    (DerivedCategory.homologyFunctor (Modules Y') 1).map
      ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
          (derivedPullbackPushforwardAdjunction (pullback.snd f g))
          (DerivedQCoh.cohomologyBaseChangeCartesianIso
            (IsPullback.of_hasPullback f g))).app OX) ≫
    (DerivedCategory.homologyFunctor (Modules Y') 1).map
      ((Modules.pushforwardDerived (pullback.snd f g)).map
        (ModuleDerived.singlePullbackComparison (pullback.fst f g)
            (SheafOfModules.unit (structureSheaf X)) 0 ≫
          (DerivedCategory.singleFunctor (Modules (pullback f g)) 0).map
            (Modules.pullbackObjUnitToUnit (pullback.fst f g))))

/-- `higherDirectImageOneBaseChangeHom` is the composite of the degree-one
truncation comparison, derived base change of `Rf_* 𝒪`, and the structure-sheaf
coefficient identification. -/
theorem higherDirectImageOneBaseChangeHom_eq {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) (g : Y' ⟶ Y) :
    higherDirectImageOneBaseChangeHom f g =
      let OX := (DerivedCategory.singleFunctor (Modules X) 0).obj
        (SheafOfModules.unit (structureSheaf X))
      let E := (Modules.pushforwardDerived f).obj OX
      (Modules.pullback g).map
          ((DerivedCategory.homologyFunctor (Modules Y) 1).map ((t.truncGEπ 1).app E)) ≫
        ModuleDerived.cohomologyPullbackComparison g ((t.truncGE 1).obj E) 1
          inferInstance inferInstance ≫
        (Functor.LeftDerived.Homotopy.TruncGE.homologyIso (Modules.pullback g)
            (ModuleDerived.pullback g) (Functor.LeftDerived.Homotopy.counit (Modules.pullback g))
            E 1 1 le_rfl).inv ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((DerivedBaseChange.map (derivedPullbackPushforwardAdjunction f)
              (derivedPullbackPushforwardAdjunction (pullback.snd f g))
              (DerivedQCoh.cohomologyBaseChangeCartesianIso
                (IsPullback.of_hasPullback f g))).app OX) ≫
        (DerivedCategory.homologyFunctor (Modules Y') 1).map
          ((Modules.pushforwardDerived (pullback.snd f g)).map
            (ModuleDerived.singlePullbackComparison (pullback.fst f g)
                (SheafOfModules.unit (structureSheaf X)) 0 ≫
              (DerivedCategory.singleFunctor (Modules (pullback f g)) 0).map
                (Modules.pullbackObjUnitToUnit (pullback.fst f g)))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
