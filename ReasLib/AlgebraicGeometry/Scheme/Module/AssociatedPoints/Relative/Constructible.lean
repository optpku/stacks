/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a finite-presentation morphism `f : X ⟶ Y`, a finitely presented module ℱ on `X`,
and an open `U ⊆ X` whose composite `U.ι ≫ f` is quasi-compact, the locus of points of `Y`
where the associated points of the pullback of ℱ to the fiber lie in the fiber of `U` is
locally constructible. -/
theorem associatedPoints_fiber_subset_isLocallyConstructible
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Scheme.Hom.FinitePresentation f]
    (ℱ : X.Modules) [ℱ.IsFinitePresentation] (U : X.Opens) [QuasiCompact (U.ι ≫ f)] :
    Topology.IsLocallyConstructible
      {y : Y | ((Scheme.Modules.pullback (f.fiberι y)).obj ℱ).associatedPoints ⊆
        (f.fiberι y) ⁻¹' (U : Set X)} := sorry

end AlgebraicGeometry.Scheme.Hom
