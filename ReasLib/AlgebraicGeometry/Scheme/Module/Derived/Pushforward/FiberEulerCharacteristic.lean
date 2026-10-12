/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.FlatCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The Euler-characteristic function of a module sheaf relative to a scheme morphism,
viewed through the derived pushforward of the sheaf placed in degree zero. -/
noncomputable def relativeEulerChar {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) : S → ℤ :=
  Scheme.ModuleDerived.fiberEulerChar
    ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ))

/-- The relative Euler-characteristic function is the derived-fiber Euler characteristic
of the degree-zero derived pushforward. -/
theorem relativeEulerChar_apply {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) (s : S) :
    relativeEulerChar f ℱ s =
      Scheme.ModuleDerived.fiberEulerChar
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)) s := sorry

/-- For a proper finitely presented morphism and a finitely presented module sheaf flat
over the base, the fiber Euler-characteristic function is locally constant. -/
theorem relativeEulerChar_isLocallyConstant {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] :
    IsLocallyConstant (relativeEulerChar f ℱ) := sorry

/-- Formation of the fiber Euler-characteristic function commutes with arbitrary base
change for a proper finitely presented morphism and finitely presented flat coefficients. -/
theorem relativeEulerChar_baseChange {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    [SheafOfModules.IsFlatOver ℱ f.toShHom]
    (sq : IsPullback g' f' f g) :
    relativeEulerChar f' ((Scheme.Modules.pullback g').obj ℱ) =
      fun s' : S' ↦ relativeEulerChar f ℱ (g s') := sorry

end AlgebraicGeometry.Scheme.Modules
