module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine
public import ReasLib.CategoryTheory.Pretriangulated.Functor.ReflectsIsomorphisms
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Adjunction

/-!
# Conservative derived pushforward

This module gives zero-object criteria for conservativity of derived quasicoherent pushforward
and records conservativity for quasi-compact open immersions and composites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn

/-- Derived pushforward along a quasi-compact, quasi-separated morphism reflects zero objects
if and only if it reflects isomorphisms. -/
theorem reflectsZero_iff_reflectsIsomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (∀ K : Scheme.ModuleDerived.Quasicoherent X,
      IsZero ((pushforwardCohomologyIn f).obj K) ↔ IsZero K) ↔
      (pushforwardCohomologyIn f).ReflectsIsomorphisms := sorry

/-- If an object weakly generates the target, derived pushforward reflects zero objects
exactly when its derived pullback weakly generates the source. -/
theorem reflectsZero_iff_pullback_isWeakGenerator
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : Scheme.ModuleDerived.Quasicoherent Y) (hE : IsWeakGenerator E) :
    (∀ K : Scheme.ModuleDerived.Quasicoherent X,
      IsZero ((pushforwardCohomologyIn f).obj K) ↔ IsZero K) ↔
      IsWeakGenerator ((pullback f).obj E) := sorry

/-- Derived pushforward along a quasi-compact open immersion reflects isomorphisms. -/
instance reflectsIsomorphisms_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsOpenImmersion f] :
    (pushforwardCohomologyIn f).ReflectsIsomorphisms := sorry

/-- Conservativity of derived pushforward is stable under composition of quasi-compact,
quasi-separated morphisms. -/
instance reflectsIsomorphisms_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
    [(pushforwardCohomologyIn f).ReflectsIsomorphisms]
    [(pushforwardCohomologyIn g).ReflectsIsomorphisms] :
    (pushforwardCohomologyIn (f ≫ g)).ReflectsIsomorphisms := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn
