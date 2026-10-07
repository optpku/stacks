module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.RingTheory.Localization.ClosedFiber
public import ReasLib.RingTheory.Flatness.LocalCriterion.ClosedFiber.RestrictScalars

/-!
# Flatness at associated points of a fiber

This module relates relative flatness at a point to relative flatness at the associated points
of its fiber that specialize to it.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite-type quasicoherent module is flat over the base at `x` if and only if it is flat at
every associated point of the fiber over `f x` whose image specializes to `x`. -/
theorem flatOverAt_iff_associatedPoints_specializingTo
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (x : X) :
    flatOverAt ℱ f x ↔
      ∀ x' : f.fiber (f x),
        x' ∈ ((Scheme.Modules.pullback (f.fiberι (f x))).obj ℱ).associatedPoints →
          f.fiberι (f x) x' ⤳ x → flatOverAt ℱ f (f.fiberι (f x) x') := sorry

end AlgebraicGeometry.Scheme.Modules
