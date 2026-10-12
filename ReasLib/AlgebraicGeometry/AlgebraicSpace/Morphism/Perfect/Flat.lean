/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.EtaleCharts
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Flat perfect morphisms of algebraic spaces

Flatness together with perfectness on étale charts is equivalent to flatness
together with local finite presentation on étale charts.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is flat and perfect on étale charts if and
only if it is flat and locally of finite presentation on étale charts. -/
theorem flat_and_perfect_iff_flat_and_locallyOfFinitePresentation
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (onEtaleCharts (@AlgebraicGeometry.Flat) f ∧
        onEtaleCharts (@AlgebraicGeometry.LocallyOfType.{u} RingHom.IsPerfectRingMap) f) ↔
      (onEtaleCharts (@AlgebraicGeometry.Flat) f ∧
        onEtaleCharts (@AlgebraicGeometry.LocallyOfFinitePresentation) f) := sorry

end AlgebraicGeometry.AlgebraicSpace
