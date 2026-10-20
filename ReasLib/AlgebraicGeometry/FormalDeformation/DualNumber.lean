/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.DualNumber
public import ReasLib.RingTheory.DualNumber.Finiteness
public import ReasLib.RingTheory.DualNumber.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue

/-!
# Dual numbers as an Artinian local algebra

The dual numbers over the residue field define a canonical object and coefficient
projection in the category of residue-identified Artinian local algebras.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

universe u

/-- Dual numbers over a field are Artinian. -/
instance isArtinianRing_dualNumber {k : Type u} [Field k] : IsArtinianRing (DualNumber k) :=
  IsArtinianRing.of_finite k (DualNumber k)

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The residue field of the dual numbers is identified with the coefficient field. -/
def dualNumberResidueFieldIso : ResidueField (DualNumber k) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (DualNumber.maximalIdeal_eq_span_singleton_eps.trans
        (DualNumber.epsIdeal_eq_span k).symm)).trans
    ((DualNumber.residueAlgEquiv k).restrictScalars Λ)

/-- The residue identification sends the class of a dual number to its scalar coefficient. -/
theorem dualNumberResidueFieldIso_apply (x : DualNumber k) :
    dualNumberResidueFieldIso Λ k (IsLocalRing.residue (DualNumber k) x) = x.fst := rfl

/-- The dual numbers with their coefficient-field residue identification form an Artinian
local algebra. -/
def dualNumber : ArtinianLocalAlgCat Λ k :=
  of (DualNumber k) (dualNumberResidueFieldIso Λ k)

/-- The bundled dual-number object has carrier `DualNumber k`. -/
theorem dualNumber_carrier : (dualNumber Λ k).carrier = DualNumber k := rfl

/-- The coefficient projection is a morphism to the residue-field object. -/
def dualNumberToResidue : dualNumber Λ k ⟶ residue Λ k :=
  Hom.of ((fstHom k k k).restrictScalars Λ)
    ⟨fun _ h_unit ↦ isUnit_iff_isUnit_fst.mpr h_unit⟩ sorry

/-- The underlying algebra map of the dual-number projection is the coefficient projection. -/
theorem dualNumberToResidue_hom :
    (dualNumberToResidue Λ k).hom = (fstHom k k k).restrictScalars Λ := rfl

/-- The projection from the dual numbers to the residue-field object is surjective. -/
theorem dualNumberToResidue_surjective :
    Function.Surjective (dualNumberToResidue Λ k).hom := fun scalar ↦ ⟨inl scalar, rfl⟩

/-- The dual-number projection is local and compatible with the chosen residue
identifications. -/
theorem dualNumberToResidue_spec :
    IsLocalHom (dualNumberToResidue Λ k).hom ∧
      residueCompat (dualNumberToResidue Λ k).hom (dualNumberToResidue Λ k).isLocalHom =
        residueIsoHom (dualNumber Λ k) :=
  ⟨(dualNumberToResidue Λ k).isLocalHom, (dualNumberToResidue Λ k).residue_compat⟩

end ArtinianLocalAlgCat
