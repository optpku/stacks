/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_11_2_Pushforward

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

/-- The unbounded derived pushforward `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of sheaves of modules. -/
abbrev pushforwardDerived (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  moduleDerivedPushforward f

/-- Derived module pushforward is the K-injective total right derived functor of `pushforward`. -/
theorem pushforwardDerived_eq (f : X ⟶ Y) :
    pushforwardDerived f =
      Functor.RightDerived.KInjective.functor.{u} (pushforward f) :=
  rfl

/-- Derived module pushforward satisfies the universal property of a right-derived functor. -/
instance pushforwardDerived_isRightDerived (f : X ⟶ Y) :
    (pushforwardDerived f).IsRightDerivedFunctor
      (Functor.RightDerived.KInjective.unit (pushforward f))
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
