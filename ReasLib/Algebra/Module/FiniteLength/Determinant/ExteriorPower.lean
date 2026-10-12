/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Dimension
public import ReasLib.Algebra.Module.Length.ResidueField
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Finite-length determinants and top exterior powers

This file constructs the comparison from the determinant-symbol quotient of a module
annihilated by the maximal ideal to its top exterior power over the residue field.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FiniteLengthDeterminant

variable (R : Type u) (M : Type v) [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M]

/-- Maximal-ideal annihilation identifies the finite-length index with residue-field
dimension. -/
theorem length_eq_finrank (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    length R M hM = Module.finrank (IsLocalRing.ResidueField R) M := sorry

/-- Every family of the required length is an admissible determinant symbol when the maximal
ideal annihilates the module. -/
theorem isAdmissible_of_isTorsionBySet (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (e : Fin (length R M hM) → M) :
    IsAdmissible R M hM e := sorry

/-- The free-symbol map sending a family to its wedge in the top exterior power. -/
def wedgeLinearMap (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    Free R M hM →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(Module.finrank (IsLocalRing.ResidueField R) M) M :=
  -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
  letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
  Finsupp.linearCombination (IsLocalRing.ResidueField R) fun e : Symbol R M hM ↦
    exteriorPower.ιMulti (IsLocalRing.ResidueField R)
      (Module.finrank (IsLocalRing.ResidueField R) M) (e.1 ∘ Fin.cast hl.symm)

/-- The free-symbol wedge map evaluates on a basis symbol by taking the corresponding wedge. -/
theorem wedgeLinearMap_single (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M)
    (e : Symbol R M hM) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    wedgeLinearMap R M hM hAnn hl (Finsupp.single e 1) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) M) (e.1 ∘ Fin.cast hl.symm) := sorry

/-- The free-symbol wedge map vanishes on every defining determinant relation. -/
theorem wedgeLinearMap_eq_zero_of_relation (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M)
    (x : Free R M hM) (hx : Relation R M hM x) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    wedgeLinearMap R M hM hAnn hl x = 0 := sorry

/-- The canonical comparison from the determinant-symbol quotient to the top exterior power. -/
def toExteriorPower (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    Module.FiniteLengthDeterminant R M hM →ₗ[IsLocalRing.ResidueField R]
      ⋀[IsLocalRing.ResidueField R]^(Module.finrank (IsLocalRing.ResidueField R) M) M :=
  -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
  letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
  lift R M hM (wedgeLinearMap R M hM hAnn hl)
    (wedgeLinearMap_eq_zero_of_relation R M hM hAnn hl)

/-- The comparison map sends an admissible determinant symbol to its reindexed wedge. -/
theorem toExteriorPower_symbol (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M)
    (e : Symbol R M hM) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    toExteriorPower R M hM hAnn hl (symbol R M hM e) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) M) (e.1 ∘ Fin.cast hl.symm) := sorry

/-- The determinant symbol associated to an arbitrary residue-field-dimension-indexed family. -/
def symbolOfFamily (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M)
    (e :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      Fin (Module.finrank (IsLocalRing.ResidueField R) M) → M) :
    Module.FiniteLengthDeterminant R M hM :=
  -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
  letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
  symbol R M hM ⟨e ∘ Fin.cast hl,
    isAdmissible_of_isTorsionBySet R M hM hAnn (e ∘ Fin.cast hl)⟩

/-- The comparison sends the determinant symbol of a family to that family's wedge. -/
theorem toExteriorPower_symbolOfFamily (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R))
    (hl :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      length R M hM = Module.finrank (IsLocalRing.ResidueField R) M)
    (e :
      -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
      letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
      Fin (Module.finrank (IsLocalRing.ResidueField R) M) → M) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    toExteriorPower R M hM hAnn hl (symbolOfFamily R M hM hAnn hl e) =
      exteriorPower.ιMulti (IsLocalRing.ResidueField R)
        (Module.finrank (IsLocalRing.ResidueField R) M) e := sorry

/-- For a finite-length module annihilated by the maximal ideal, the canonical comparison from
determinant symbols to the top exterior power over the residue field is bijective. -/
theorem toExteriorPower_bijective (hM : IsFiniteLength R M)
    (hAnn : Module.IsTorsionBySet R M (IsLocalRing.maximalIdeal R)) :
    -- Local instance justification (search instability): `hAnn` determines this action but cannot be inferred.
    letI : Module (IsLocalRing.ResidueField R) M := hAnn.module
    Function.Bijective
      (toExteriorPower R M hM hAnn (length_eq_finrank R M hM hAnn)) := sorry

end Module.FiniteLengthDeterminant
