module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
public import stacks_project.Chap76.Definition_76_7_2_Differentials

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

/-- Lemma 76.14.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is formally unramified if and only if the
sheaf of relative differentials `Ω[f]` vanishes. -/
@[stacks 04G9]
theorem formallyUnramified_iff_isZero_relativeDifferentials
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    FormallyUnramified f ↔ IsZero (Ω[f]) :=
  sorry

namespace FormallyUnramified

/-- The sheaf of relative differentials of a formally unramified morphism of
algebraic spaces vanishes. -/
theorem isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} [FormallyUnramified f] : IsZero (Ω[f]) :=
  sorry

/-- A morphism of algebraic spaces whose sheaf of relative differentials vanishes
is formally unramified. -/
theorem of_isZero_relativeDifferentials {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : X ⟶ Y} (h : IsZero (Ω[f])) : FormallyUnramified f :=
  sorry

end FormallyUnramified

end AlgebraicGeometry.AlgebraicSpace
