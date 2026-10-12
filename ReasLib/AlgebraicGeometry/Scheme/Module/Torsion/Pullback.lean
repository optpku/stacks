/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Torsion.FlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Torsion-freeness under pullback

This file records preservation of torsion-freeness for quasicoherent module sheaves pulled back
along flat morphisms of integral schemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsTorsionFree

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- Pullback along a flat morphism of integral schemes preserves torsion-freeness of a
quasicoherent module sheaf. -/
theorem pullback
    (f : X ⟶ Y) [Flat f] {ℱ : Y.Modules} [ℱ.IsQuasicoherent]
    (hℱ : IsTorsionFree ℱ) :
    IsTorsionFree ((Scheme.Modules.pullback f).obj ℱ) := sorry

/-- The pullback of a torsion-free quasicoherent module sheaf along a flat morphism of integral
schemes is canonically torsion free. -/
instance instIsTorsionFree_pullback
    (f : X ⟶ Y) [Flat f] {ℱ : Y.Modules} [ℱ.IsQuasicoherent] [hℱ : IsTorsionFree ℱ] :
    IsTorsionFree ((Scheme.Modules.pullback f).obj ℱ) :=
  pullback f hℱ

end AlgebraicGeometry.Scheme.Modules.IsTorsionFree
