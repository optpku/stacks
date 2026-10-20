/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Qcqs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RestrictedPushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.CategoryTheory.Pretriangulated.Generation.Orthogonal

/-!
# Conservativity of derived pushforward on algebraic spaces

Restricted derived pushforward on complexes with quasi-coherent cohomology
reflects zero objects if and only if it reflects isomorphisms. Given a weak
generator on the target, these conditions are equivalent to its derived pullback
weakly generating the source. Affine morphisms, quasi-compact open immersions,
and composites of conservative quasi-compact, quasi-separated morphisms have
conservative derived pushforward.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward

/-- Derived pushforward along a quasi-compact, quasi-separated morphism of algebraic
spaces reflects zero objects if and only if it reflects isomorphisms. -/
theorem reflectsZero_iff_reflectsIsomorphisms {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (∀ K : DerivedQCoh X, IsZero ((pushforwardCohomologyIn f).obj K) ↔ IsZero K) ↔
      (pushforwardCohomologyIn f).ReflectsIsomorphisms := sorry

/-- If an object weakly generates the target, derived pushforward reflects zero objects
exactly when its derived pullback weakly generates the source. -/
theorem reflectsZero_iff_pullback_isWeakGenerator {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedQCoh Y) (hE : IsWeakGenerator E) :
    (∀ K : DerivedQCoh X, IsZero ((pushforwardCohomologyIn f).obj K) ↔ IsZero K) ↔
      IsWeakGenerator ((AlgebraicSpace.DerivedQCoh.pullback f).obj E) := sorry

/-- Restricted derived pushforward along an affine morphism of algebraic spaces
reflects isomorphisms. -/
instance reflectsIsomorphisms_of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] :
    (pushforwardCohomologyIn f).ReflectsIsomorphisms :=
  sorry

/-- Derived pushforward along a quasi-compact open immersion of algebraic spaces
reflects isomorphisms. -/
instance reflectsIsomorphisms_of_isOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [IsOpenImmersion f] :
    (pushforwardCohomologyIn f).ReflectsIsomorphisms := sorry

/-- Conservativity of derived pushforward is stable under composition of quasi-compact,
quasi-separated morphisms of algebraic spaces. -/
instance reflectsIsomorphisms_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g]
    [(pushforwardCohomologyIn f).ReflectsIsomorphisms]
    [(pushforwardCohomologyIn g).ReflectsIsomorphisms] :
    (pushforwardCohomologyIn (f ≫ g)).ReflectsIsomorphisms := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforward
