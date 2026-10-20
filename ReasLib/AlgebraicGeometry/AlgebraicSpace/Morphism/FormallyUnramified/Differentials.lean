module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials

/-!
# Formal unramifiedness and vanishing of relative differentials

A morphism of algebraic spaces is formally unramified if and only if its sheaf
of relative differentials vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits
open scoped AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is formally unramified if and
only if its sheaf of relative differentials vanishes. -/
theorem formallyUnramified_iff_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyUnramified f ↔ IsZero (Ω[f]) :=
  sorry

namespace FormallyUnramified

/-- The sheaf of relative differentials of a formally unramified morphism of
algebraic spaces vanishes. -/
theorem isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyUnramified f] : IsZero (Ω[f]) :=
  (formallyUnramified_iff_isZero_relativeDifferentials f).mp inferInstance

/-- A morphism of algebraic spaces whose sheaf of relative differentials vanishes
is formally unramified. -/
theorem of_isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (h : IsZero (Ω[f])) : FormallyUnramified f :=
  (formallyUnramified_iff_isZero_relativeDifferentials f).mpr h

end FormallyUnramified

end AlgebraicGeometry.AlgebraicSpace
