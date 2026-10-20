module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.AssociatedPoints

/-!
# Flatness and the relative assassin

This module gives global flatness criteria in terms of specialization from the relative assassin
to a fiber.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.relativeAssassin

/-- A finite-type quasicoherent module is flat over the base if it is flat along one fiber and
every point of its relative assassin specializes to that fiber. -/
theorem flatOver_of_specializesTo_fiber
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (h_ass : ∀ x ∈ relativeAssassin f ℱ, ∃ z : f.fiber s, x ⤳ f.fiberι s z)
    (h_flat : ∀ z : f.fiber s, flatOverAt ℱ f (f.fiberι s z)) :
    flatOver ℱ f := sorry

/-- A finite-type quasicoherent module over a locally finite-type morphism to a local scheme is
flat over the base if it is flat along its closed fiber and every point of its relative assassin
specializes to that fiber. -/
theorem flatOver_of_specializesTo_closedFiber
    {X S : Scheme.{u}} [IsAffine S] [IsLocalRing Γ(S, ⊤)]
    (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (s : S)
    (hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    (h_ass : ∀ x ∈ relativeAssassin f ℱ, ∃ z : f.fiber s, x ⤳ f.fiberι s z)
    (h_flat : ∀ z : f.fiber s, flatOverAt ℱ f (f.fiberι s z)) :
    flatOver ℱ f := sorry

end AlgebraicGeometry.Scheme.Modules.relativeAssassin
