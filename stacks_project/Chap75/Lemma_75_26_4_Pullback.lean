module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Lemma_75_5_2_EtaleLocal

/-!
# Derived pullback of modules along morphisms of algebraic spaces

An arbitrary morphism of algebraic spaces induces the unbounded derived inverse image
`Lf^*` as the total left derived functor of module pullback. Étale morphisms already have
an exact derived pullback; the two agree up to isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Module pullback along an arbitrary morphism of algebraic spaces is additive. -/
instance instPullbackAdditive {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (pullback f).Additive :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quasi-isomorphisms used to localize the homotopy category of `𝒪_X`-modules. -/
abbrev ModuleQis {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  HomotopyCategory.quasiIso (Modules X) (up ℤ)

/-- The homotopy-to-derived functor induced by module pullback along a morphism of
algebraic spaces. -/
abbrev modulePullbackToDerived {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived Y :=
  Functor.Homotopy.toDerived (Modules.pullback f)

/-- Module pullback on homotopy categories admits an everywhere defined total left derived
functor. -/
instance instModulePullbackToDerivedHasLeftDerivedFunctor
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis X) :=
  sorry

/-- The unbounded derived pullback functor `Lf^*` on module sheaves over algebraic spaces. -/
def modulePullbackDerived {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis X)

/-- Derived pullback is the total left derived functor of homotopy-level module pullback. -/
theorem modulePullbackDerived_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    modulePullbackDerived f =
      (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis X) :=
  sorry

namespace modulePullbackDerived

/-- Derived pullback satisfies the universal property of a left derived functor. -/
instance isLeftDerivedFunctor {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (modulePullbackDerived f).IsLeftDerivedFunctor
      ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis X))
      (ModuleQis X) :=
  sorry

end modulePullbackDerived

/-- On étale morphisms, unbounded derived pullback agrees with exact derived pullback. -/
theorem modulePullbackDerived_etale {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    (f : Y ⟶ X) [Etale f] :
    IsIsomorphic (modulePullbackDerived f) (ModuleDerived.pullback f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
