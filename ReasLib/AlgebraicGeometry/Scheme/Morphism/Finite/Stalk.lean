/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pushforward.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Stalks of finite morphisms

This file records finiteness properties of stalk maps at singleton fibers and the corresponding
isomorphism between the stalk of a pushforward module and the original stalk.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.IsFinite

/-- The local-ring map of a finite morphism is finite at a point that is alone in its fiber. -/
@[stacks 05B8]
theorem stalkMap_finite_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}) :
    (f.stalkMap x).hom.Finite := sorry

/-- The local-ring map of a finite morphism of finite presentation is finitely presented at a
point that is alone in its fiber. -/
@[stacks 05B8]
theorem stalkMap_finitePresentation_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Scheme.Hom.FinitePresentation f]
    (x : X) (h_fiber : f ⁻¹' {f x} = {x}) :
    (f.stalkMap x).hom.FinitePresentation := sorry

/-- For a quasicoherent module and a point that is alone in its fiber under a finite morphism,
the canonical map from the pushforward stalk to the original stalk is an isomorphism after
restriction of scalars along the local-ring map. -/
@[stacks 05B8]
theorem stalkPushforward_isIso_of_fiber_eq_singleton
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (h_fiber : f ⁻¹' {f x} = {x}) (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsIso (Scheme.Modules.stalkPushforward f ℱ x) := sorry

end AlgebraicGeometry.IsFinite
