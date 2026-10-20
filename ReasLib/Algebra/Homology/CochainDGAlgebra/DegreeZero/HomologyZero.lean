/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.HomologyZero
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Zeroth cohomology of an ordinary algebra model

The degree-zero DGA model of an ordinary algebra is a useful boundary between the ordinary and
DG APIs.  This leaf owns the algebra equivalence on zeroth cohomology explicitly, so downstream
Morita statements can transport their prescribed endomorphism algebra without inspecting the
single-term complex.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CochainDGAlgebra

variable (R : Type u) [CommRing R]
variable (A : Type v) [Ring A] [Algebra R A]

/-- Zeroth cohomology of the degree-zero DGA model is canonically the original algebra. -/
@[stacks 09SC "ordinary algebra recovered from its degree-zero DGA"]
noncomputable def homologyZeroEquiv :
    (ofAlgebra R A).homologyZero ≃ₐ[R] A where
  toFun := fun x ↦ (ofAlgebraZeroIso R A).hom
    ((IsConcentratedInDegreeZero.homologyZeroIso
      (A := ofAlgebra R A) (ofAlgebra_isConcentratedInDegreeZero R A)).hom x)
  invFun := fun x ↦ (IsConcentratedInDegreeZero.homologyZeroIso
      (A := ofAlgebra R A) (ofAlgebra_isConcentratedInDegreeZero R A)).inv
    ((ofAlgebraZeroIso R A).inv x)
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry
  map_mul' := sorry
  commutes' := sorry

/-- The forward map of `homologyZeroEquiv` is the canonical module isomorphism. -/
@[simp]
theorem homologyZeroEquiv_apply (x : (ofAlgebra R A).homologyZero) :
    homologyZeroEquiv R A x = (ofAlgebraZeroIso R A).hom
      ((IsConcentratedInDegreeZero.homologyZeroIso
        (A := ofAlgebra R A) (ofAlgebra_isConcentratedInDegreeZero R A)).hom x) := rfl

/-- The inverse map of `homologyZeroEquiv` is the inverse canonical module isomorphism. -/
@[simp]
theorem homologyZeroEquiv_symm_apply (x : A) :
    (homologyZeroEquiv R A).symm x =
      (IsConcentratedInDegreeZero.homologyZeroIso
        (A := ofAlgebra R A) (ofAlgebra_isConcentratedInDegreeZero R A)).inv
        ((ofAlgebraZeroIso R A).inv x) := rfl

end CochainDGAlgebra
