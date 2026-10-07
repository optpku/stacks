module

public import ReasLib.Algebra.Module.End.FiniteLength
public import ReasLib.Algebra.Module.Length.Semilocal
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.Tactic.CrossRefAttribute

/-!
# Norm formula for finite-length determinants

This leaf identifies scalar multiplication on a finite-length module over a local extension with
the residue-field norm.

@stack 0GSZ
-/

@[expose] public section

noncomputable section

open IsLocalRing

universe u v w

variable {R : Type u} {R' : Type v} {M' : Type w}
variable [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R']
variable [Algebra R R'] [IsLocalHom (algebraMap R R')]
variable [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

local notation "κ" => ResidueField R
local notation "κ'" => ResidueField R'

/-- Finite length descends along a local homomorphism with finite residue-field extension. -/
@[stacks 0GSZ "finite length after local restriction of scalars"]
theorem IsLocalRing.isFiniteLength_restrictScalars [Module.Finite κ κ']
    (hM' : IsFiniteLength R' M') : IsFiniteLength R M' := sorry
-- Proof strategy: specialize `Module.isFiniteLength_restrictScalars_of_residueFinite`; the local
-- target has a single maximal ideal over `maximalIdeal R`, and its residue-field map is finite by
-- the supplied `Module.Finite κ κ'` instance.

namespace Module.End

/-- Lemma 15.121.2 (0GSZ): the finite-length determinant of multiplication by `u` is the
residue-field norm of `u` raised to the module length. -/
@[stacks 0GSZ "Lemma 15.121.2: determinant of scalar multiplication"]
theorem finiteLengthDeterminant_algebraLsmul_eq_norm_pow_length
    [Module.Finite κ κ'] (u : R') (hM' : IsFiniteLength R' M') :
    (Algebra.lsmul R R M' u).finiteLengthDeterminant
        (IsLocalRing.isFiniteLength_restrictScalars hM') =
      Algebra.norm κ (IsLocalRing.residue R' u) ^ (Module.length R' M').toNat := sorry
-- Proof strategy: compute the determinant on an `R'`-composition series via
-- `finiteLengthDeterminant_eq_det`; every simple factor contributes the determinant of
-- multiplication by `IsLocalRing.residue R' u` on `κ'` over `κ`, namely its field norm, and the
-- number of factors is `(Module.length R' M').toNat`.

end Module.End

end
