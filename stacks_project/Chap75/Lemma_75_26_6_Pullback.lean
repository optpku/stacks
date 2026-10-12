/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Ext.TStructure
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap69.Lemma_69_11_2_Flat_base_change_BaseChange
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Derived pullback of modules on algebraic spaces

General derived pullback `Lf*` on `D(𝒪_X)` is the total left derived functor of
underived module pullback. This is the algebraic-space analogue of
`RingedSpace.modulePullbackDerived`, and does not use the `UnivLE`-gated topos
derived pullback on `ringedSite X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Module sheaves on an algebraic space carry the homology structure induced by their
abelian structure. -/
instance modulesCategoryWithHomology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    CategoryWithHomology (Modules X) :=
  CategoryTheory.categoryWithHomology_of_abelian

namespace Modules

/-- Module pullback along an arbitrary morphism of algebraic spaces is additive. -/
instance instAdditive_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pullback f).Additive :=
  sorry

end Modules

namespace ModuleDerived

/-- Homotopy-to-derived module pullback along an arbitrary morphism of algebraic spaces
has a total left derived functor. -/
instance instHasLeftDerivedFunctor_toDerived_pullback
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (Functor.Homotopy.toDerived (Modules.pullback f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (Modules X) (up ℤ)) :=
  sorry

/-- Derived pullback `Lf* : D(𝒪_X) ⥤ D(𝒪_Y)` along a morphism of algebraic spaces. -/
def pullback {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.LeftDerived.Homotopy.functor (Modules.pullback f)

/-- Derived pullback is the total left derived functor of underived module pullback. -/
theorem pullback_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    pullback f = Functor.LeftDerived.Homotopy.functor (Modules.pullback f) :=
  sorry

/-- Étale module pullback preserves finite limits. -/
instance instPreservesFiniteLimits_pullback_of_etale
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) [AlgebraicSpace.Etale f] :
    PreservesFiniteLimits (Modules.pullback f) :=
  sorry

/-- Étale module pullback preserves finite colimits. -/
instance instPreservesFiniteColimits_pullback_of_etale
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) [AlgebraicSpace.Etale f] :
    PreservesFiniteColimits (Modules.pullback f) :=
  sorry

/-- On étale morphisms, general derived pullback agrees with `mapDerivedCategory` of
module pullback. -/
theorem pullback_eq_mapDerivedCategory {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) [AlgebraicSpace.Etale f] :
    pullback f = (Modules.pullback f).mapDerivedCategory :=
  sorry

/-- The canonical comparison from the composite of derived pullbacks to derived pullback
along the composite morphism. -/
def pullbackCompComparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    pullback g ⋙ pullback f ⟶ pullback (f ≫ g) :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
    (Modules.pullbackCompIso f g).symm

/-- The composition comparison is the canonical total-left-derived composition comparison
of module pullbacks. -/
theorem pullbackCompComparison_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    pullbackCompComparison f g =
      Functor.LeftDerived.Homotopy.Composition.comparison
        (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
        (Modules.pullbackCompIso f g).symm :=
  sorry

/-- The canonical comparison from derived pullback of a single sheaf in degree `i` to the
ordinary pullback placed in the same degree. -/
def singlePullbackComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S} (g : Y ⟶ X)
    (M : X.Modules) (i : ℤ) :
    (pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M) ⟶
      (DerivedCategory.singleFunctor (Modules Y) i).obj ((Modules.pullback g).obj M) :=
  let SM := (CochainComplex.singleFunctor (Modules X) i).obj M
  (pullback g).map ((DerivedCategory.singleFunctorIsoCompQ (Modules X) i).hom.app M) ≫
    (pullback g).map ((DerivedCategory.quotientCompQhIso (Modules X)).inv.app SM) ≫
      (Functor.LeftDerived.Homotopy.counit (Modules.pullback g)).app
          ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj SM) ≫
        (Functor.Homotopy.singleIso (Modules.pullback g) i).hom.app M

/-- The single-sheaf comparison is obtained from the derived-functor counit and the
homotopy-to-derived single-object identification. -/
theorem singlePullbackComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    singlePullbackComparison g M i =
      let SM := (CochainComplex.singleFunctor (Modules X) i).obj M
      (pullback g).map ((DerivedCategory.singleFunctorIsoCompQ (Modules X) i).hom.app M) ≫
        (pullback g).map ((DerivedCategory.quotientCompQhIso (Modules X)).inv.app SM) ≫
          (Functor.LeftDerived.Homotopy.counit (Modules.pullback g)).app
              ((HomotopyCategory.quotient (Modules X) (up ℤ)).obj SM) ≫
            (Functor.Homotopy.singleIso (Modules.pullback g) i).hom.app M :=
  sorry

/-- On degree-`i` homology, derived pullback of a single sheaf canonically recovers ordinary
pullback. -/
def singlePullbackHomologyComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    (DerivedCategory.homologyFunctor (Modules Y) i).obj
        ((pullback g).obj ((DerivedCategory.singleFunctor (Modules X) i).obj M)) ⟶
      (Modules.pullback g).obj M :=
  (DerivedCategory.homologyFunctor (Modules Y) i).map (singlePullbackComparison g M i) ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Y) i).hom.app
      ((Modules.pullback g).obj M)

/-- The single-sheaf homology comparison is homology of `singlePullbackComparison` followed
by removing the single-complex realization. -/
theorem singlePullbackHomologyComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    singlePullbackHomologyComparison g M i =
      (DerivedCategory.homologyFunctor (Modules Y) i).map (singlePullbackComparison g M i) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules Y) i).hom.app
          ((Modules.pullback g).obj M) :=
  sorry

/-- The single-sheaf pullback homology comparison is invertible. -/
instance singlePullbackHomologyComparison_isIso {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (M : X.Modules) (i : ℤ) :
    IsIso (singlePullbackHomologyComparison g M i) :=
  sorry

/-- The lowest potentially nonzero cohomology sheaf of a bounded-below derived module maps
canonically into that derived module. -/
def lowerCohomologyInclusion {S : Scheme.{u}} {X : AlgebraicSpace S}
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a) :
    (DerivedCategory.singleFunctor (Modules X) a).obj
        ((DerivedCategory.homologyFunctor (Modules X) a).obj E) ⟶ E :=
  (CategoryTheory.ShiftedHom.homEquiv (a - a) (sub_self a)).symm
    ((DerivedCategory.ShiftedHom.Boundary.toHomologyEquiv
      ((DerivedCategory.singleFunctor (Modules X) a).obj
        ((DerivedCategory.homologyFunctor (Modules X) a).obj E))
      E a a inferInstance hE).symm
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Modules X) a).hom.app
        ((DerivedCategory.homologyFunctor (Modules X) a).obj E)))

/-- The canonical lower-edge comparison maps ordinary pullback of degree-`a` cohomology to
degree-`a` cohomology after derived pullback. -/
def cohomologyPullbackComparison {S : Scheme.{u}} {Y X : AlgebraicSpace S} (g : Y ⟶ X)
    (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a)) :
    (Modules.pullback g).obj ((DerivedCategory.homologyFunctor (Modules X) a).obj E) ⟶
      (DerivedCategory.homologyFunctor (Modules Y) a).obj ((pullback g).obj E) :=
  inv (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a) ≫
    (DerivedCategory.homologyFunctor (Modules Y) a).map
      ((pullback g).map (lowerCohomologyInclusion E a hE))

/-- The lower-edge pullback comparison is the inverse single-sheaf comparison followed by
homology of the pulled-back lower cohomology inclusion. -/
theorem cohomologyPullbackComparison_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (g : Y ⟶ X) (E : ModuleDerived X) (a : ℤ) (hE : E.IsGE a)
    (hSingle : IsIso (singlePullbackHomologyComparison g
      ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a)) :
    cohomologyPullbackComparison g E a hE hSingle =
      inv (singlePullbackHomologyComparison g
          ((DerivedCategory.homologyFunctor (Modules X) a).obj E) a) ≫
        (DerivedCategory.homologyFunctor (Modules Y) a).map
          ((pullback g).map (lowerCohomologyInclusion E a hE)) :=
  sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
