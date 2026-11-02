/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.KFlat
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# K-Flat Degree-Zero Cochain Differential Graded Algebras

This leaf characterizes K-flatness of the cochain DGA canonically associated to an ordinary
algebra in terms of flatness of its underlying module over the ground ring.
-/

noncomputable section

universe u v

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- An ordinary algebra, regarded as a DGA concentrated in degree zero, is K-flat exactly when
its underlying module over the base ring is flat, provided the base ring fits in the universe used
for the K-flat test complexes.  The size premise is essential: without it, K-flatness only tests
complexes in the coefficient universe and can miss non-flat maps over a larger ring. -/
@[stacks 09SC "flat ordinary algebra as a K-flat degree-zero DGA"]
theorem ofAlgebra_isKFlat_iff (A : Type v) [Ring A] [Algebra R A] [Small.{v} R] :
    (ofAlgebra R A).IsKFlat ↔ Module.Flat R A := sorry

/-- An arbitrary-universe version is obtained by lifting the coefficient algebra into the maximum
universe.  `ULift.algebra`, `ULift.moduleEquiv`, and the canonical `ofAlgebra` construction supply
the underlying algebra and its flatness-preserving equivalence; no second K-flat predicate is
introduced. -/
theorem ofAlgebra_isKFlat_iff_ulift (A : Type v) [Ring A] [Algebra R A] :
    (ofAlgebra R (ULift.{u} A)).IsKFlat ↔ Module.Flat R A := by
  letI : Small.{max u v} R := Small.mk' (Equiv.ulift : ULift.{v} R ≃ R).symm
  calc
    (ofAlgebra R (ULift.{u} A)).IsKFlat ↔ Module.Flat R (ULift.{u} A) :=
      ofAlgebra_isKFlat_iff (R := R) (ULift.{u} A)
    _ ↔ Module.Flat R A :=
      Module.Flat.equiv_iff
        (ULift.moduleEquiv (R := R) : ULift.{u} A ≃ₗ[R] A)

/-- A flat ordinary algebra gives a K-flat degree-zero DGA. -/
@[stacks 09SC "flat ordinary algebra gives a K-flat degree-zero DGA"]
theorem ofAlgebra_isKFlat (A : Type v) [Ring A] [Algebra R A] [Module.Flat R A] :
    (ofAlgebra R A).IsKFlat := sorry

end CochainDGAlgebra
