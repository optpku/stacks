/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

/-- A proper scheme over a field is Noetherian. -/
instance AlgebraicGeometry.SchemeOverField.instIsNoetherianOfProper
    {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom] :
    IsNoetherian P.left := sorry
