module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Grothendieck
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic

/-! # Unbounded derived pushforward of modules on algebraic spaces

Module pushforward and its K-injective total right-derived functor, with the
canonical cochain comparison and universal property.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Module pushforward along a morphism of algebraic spaces is additive. -/
instance pushforward.additive {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pushforward f).Additive :=
  sorry

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
