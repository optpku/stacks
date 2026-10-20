/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Bounded.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Fiber.Point
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-!
# Fibrewise boundedness criterion for relative perfectness

For a pseudo-coherent derived module on an algebraic space flat and locally of finite
presentation over a scheme, relative perfectness is characterized by local boundedness
below of the module and of its derived restrictions to the scheme-theoretic fibres.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- A pseudo-coherent derived module on an algebraic space flat and locally of finite
presentation over a scheme is relatively perfect if and only if it and its derived
pullbacks to all scheme-theoretic fibres are locally bounded below. -/
theorem isPerfectRelativeTo_iff_locallyBoundedBelow_and_fiber
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Flat (SchemeRealization.toBase X)]
    [LocallyOfFinitePresentation (SchemeRealization.toBase X)]
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) :
    IsPerfectRelativeTo (SchemeRealization.toBase X) E ↔
      IsLocallyBoundedBelow E ∧
        ∀ s : S, IsLocallyBoundedBelow
          ((pullback (fiberι (SchemeRealization.toBase X) s)).obj E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
