module

public import stacks_project.Chap75.Lemma_75_11_2_Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward

/-!
# Derived pushforward of modules on algebraic spaces

The unbounded derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` is the K-injective total right
derived functor of module pushforward on the small étale ringed sites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Compatibility name for the unbounded derived pushforward of sheaves of modules. -/
abbrev pushforwardDerived (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  moduleDerivedPushforward f

#check (pushforwardDerived : ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S},
  (X ⟶ Y) → ModuleDerived X ⥤ ModuleDerived Y)
#check (moduleDerivedPushforward.isRightDerived : ∀ {S : Scheme.{u}}
  {X Y : AlgebraicGeometry.AlgebraicSpace S} (f : X ⟶ Y),
  (moduleDerivedPushforward f).IsRightDerivedFunctor
    (moduleDerivedPushforward.unit f)
    (HomologicalComplex.quasiIso X.Modules (up ℤ)))

end AlgebraicGeometry.AlgebraicSpace.Modules
