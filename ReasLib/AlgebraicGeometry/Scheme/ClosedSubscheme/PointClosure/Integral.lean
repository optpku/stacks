/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PointClosure

/-- A reduced point closure is an integral scheme. -/
instance scheme_isIntegral {X : Scheme.{u}} (x : X) : IsIntegral (scheme x) := sorry

/-- The canonical map between reduced point closures induced by a scheme morphism is dominant. -/
instance map_isDominant {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    IsDominant (map f x) := sorry

end AlgebraicGeometry.Scheme.PointClosure
