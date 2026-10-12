/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Complex.Basic
public import ReasLib.AlgebraicGeometry.PuncturedAffineSpace.FinitePoints
import StacksCheckRecall

/-!
# Exercise 111.55.8

The complement of finitely many points of `Fin 2 → ℂ` in the affine plane over `ℂ` is a union
of two affine opens.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

/- Exercise 111.55.8: given finitely many points of `Fin 2 → ℂ`, the scheme
`AlgebraicGeometry.PuncturedAffinePlane.affinePlane ℂ`
minus the corresponding closed points is a union of two affine opens. -/
@[stacks 07DM] #check
  (AlgebraicGeometry.PuncturedAffinePlane.exists_isAffineOpen_sup_eq_complementOpen :
    ∀ {ι : Type} [Finite ι] (p : ι → Fin 2 → ℂ),
    ∃ U V : (AlgebraicGeometry.PuncturedAffinePlane.affinePlane ℂ).Opens,
      IsAffineOpen U ∧ IsAffineOpen V ∧
        U ⊔ V = AlgebraicGeometry.PuncturedAffinePlane.complementOpen p)
