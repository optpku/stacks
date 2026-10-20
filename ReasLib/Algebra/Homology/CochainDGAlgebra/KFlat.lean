/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat
public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Flat Cochain Differential Graded Algebras

This core leaf exposes K-flatness of a cochain differential graded algebra through
its underlying cochain complex.  Compatibility with the ambient monoidal tensor product
and with degree-zero algebras lives in separate downstream leaves.
@stack 06XZ
-/

noncomputable section

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- A cochain differential graded algebra is K-flat when its underlying cochain complex is
K-flat over the ground ring. -/
@[stacks 06XZ "cochain differential graded algebra over a ring"]
def IsKFlat (A : CochainDGAlgebra.{u, v} R) : Prop :=
  A.toCochainComplex.IsKFlatOver

/-- K-flatness of a cochain differential graded algebra is K-flatness of its underlying cochain
complex over the ground ring. -/
theorem isKFlat_iff (A : CochainDGAlgebra.{u, v} R) :
    A.IsKFlat ↔ A.toCochainComplex.IsKFlatOver := sorry

end CochainDGAlgebra
