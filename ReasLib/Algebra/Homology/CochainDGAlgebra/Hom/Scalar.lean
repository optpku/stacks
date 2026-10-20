/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom

/-!
# The Base-Ring Map of a Cochain DGA

Every cochain differential graded algebra over `R` receives a canonical DGA homomorphism from
`R`, regarded as a DGA concentrated in degree zero.  This leaf owns that map and its naturality;
change-of-rings constructions can therefore depend on a named algebra map instead of rebuilding
the scalar action locally.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace CochainDGAlgebra.Hom

variable {R : Type u} [CommRing R]

/-- Multiplication of the unit by a scalar, as a linear map into degree zero of a cochain DGA. -/
def baseLinearMap (A : CochainDGAlgebra.{u, v} R) : R →ₗ[R] A.X 0 :=
  (LinearMap.id : R →ₗ[R] R).smulRight A.one

/-- The degreewise cochain-map component of the canonical base-ring map. -/
noncomputable def fromBaseComponent (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (CochainDGAlgebra.ofAlgebra R R).X n →ₗ[R] A.X n :=
  if h : n = 0 then
    { toFun := fun x ↦
        eqToHom (congrArg A.X h.symm)
          (baseLinearMap A
            ((CochainDGAlgebra.ofAlgebraZeroIso R R).hom
              (eqToHom
                (congrArg (fun i : ℤ ↦ (CochainDGAlgebra.ofAlgebra R R).X i) h) x)))
      map_add' := sorry
      map_smul' := sorry }
  else 0

/-- The canonical DGA homomorphism from the base ring, concentrated in degree zero, to `A`. -/
@[stacks 0BYZ "base-ring map into a cochain differential graded algebra"]
noncomputable def fromBase (A : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.Hom (CochainDGAlgebra.ofAlgebra R R) A where
  map := fromBaseComponent A
  comm_d := sorry
  map_one := sorry
  map_mul := sorry

/-- The base-ring map sends `r` in degree zero to `r • 1`. -/
@[simp]
theorem fromBase_apply (A : CochainDGAlgebra.{u, v} R) (r : R) :
    fromBase A 0 ((CochainDGAlgebra.ofAlgebraZeroIso R R).inv r) = r • A.one := sorry

/-- Away from degree zero, the canonical base-ring map has zero degreewise component. -/
theorem fromBase_component_eq_zero (A : CochainDGAlgebra.{u, v} R) (n : ℤ) (h : n ≠ 0) :
    (fromBase A).map n = 0 := sorry

/-- Every cochain-DGA homomorphism commutes with the canonical map from the base ring. -/
@[simp]
theorem comp_fromBase {A : CochainDGAlgebra.{u, v} R}
    {B : CochainDGAlgebra.{u, w} R} (f : CochainDGAlgebra.Hom A B) :
    comp f (fromBase A) = fromBase B := sorry

end CochainDGAlgebra.Hom
