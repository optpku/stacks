module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.TotalComposition

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
def instModulePullbackToDerivedHasLeftDerivedFunctor
    {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis X) :=
  ModuleDerived.instHasLeftDerivedFunctor_toDerived_pullback f

/-- The unbounded derived pullback functor `Lf^*` on module sheaves over algebraic spaces. -/
def modulePullbackDerived {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis X)

/-- Derived pullback is the total left derived functor of homotopy-level module pullback. -/
theorem modulePullbackDerived_eq {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X) :
    modulePullbackDerived f =
      (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis X) :=
  rfl

/-- Derived module pullback along a composite is canonically isomorphic to
the composite of the derived pullbacks, in reverse order. -/
def modulePullbackDerived.compIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    modulePullbackDerived g ⋙ modulePullbackDerived f ≅ modulePullbackDerived (f ≫ g) :=
  ModuleDerived.totalPullbackCompIso f g

/-- The canonical comparison from iterated derived module pullback to derived
module pullback along the composite morphism. -/
def modulePullbackDerived.compComparison {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : Y ⟶ Z) (g : Z ⟶ X) :
    modulePullbackDerived g ⋙ modulePullbackDerived f ⟶ modulePullbackDerived (f ≫ g) :=
  ModuleDerived.totalPullbackCompComparison f g

/-- The composition comparison of derived module pullbacks is invertible for
arbitrary morphisms of algebraic spaces. -/
instance modulePullbackDerived.compComparison_isIso
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X) :
    IsIso (modulePullbackDerived.compComparison f g) :=
  ModuleDerived.totalPullbackCompComparison_isIso f g

/-- The composition comparison agrees with the canonical total-left-derived
composition comparison of module pullbacks. -/
theorem modulePullbackDerived.compComparison_eq
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : Y ⟶ Z) (g : Z ⟶ X) :
    modulePullbackDerived.compComparison f g =
      Functor.LeftDerived.Homotopy.Composition.comparison
        (Modules.pullback f) (Modules.pullback g) (Modules.pullback (f ≫ g))
        (Modules.pullbackCompIso f g).symm :=
  ModuleDerived.totalPullbackCompComparison_eq f g

end AlgebraicGeometry.AlgebraicSpace

