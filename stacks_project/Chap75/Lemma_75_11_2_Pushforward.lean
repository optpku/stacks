/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_11_2_Coherator

/-!
# Derived module pushforward on algebraic spaces

The unbounded derived direct image `Rf_*` is the K-injective total right-derived
functor of module pushforward on the small étale ringed sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The unbounded derived pushforward of sheaves of modules along a morphism of
algebraic spaces. -/
noncomputable abbrev moduleDerivedPushforward {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    ModuleDerived X ⥤ ModuleDerived Y :=
  Functor.RightDerived.KInjective.functor.{u} (pushforward f)

namespace moduleDerivedPushforward

/-- The cochain-level comparison unit for derived module pushforward. -/
noncomputable abbrev unit {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforward f).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex (Modules Y) ℤ ⥤ DerivedCategory (Modules Y)) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        moduleDerivedPushforward f :=
  Functor.RightDerived.KInjective.unit.{u} (pushforward f)

/-- Derived module pushforward satisfies the universal property of a right-derived
functor. -/
instance isRightDerived {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (moduleDerivedPushforward f).IsRightDerivedFunctor (unit f)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)) :=
  Functor.RightDerived.KInjective.isRightDerived (pushforward f)

end moduleDerivedPushforward

end AlgebraicGeometry.AlgebraicSpace.Modules
