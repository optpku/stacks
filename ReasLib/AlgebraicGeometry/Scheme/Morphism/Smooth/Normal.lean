/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Regularity
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Normal

/-!
# Normality of smooth scheme morphisms

Smooth morphisms of schemes are normal.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A smooth morphism of schemes is normal. -/
instance instNormalOfSmooth (f : X ⟶ Y) [Smooth f] : Normal f := sorry

end AlgebraicGeometry
