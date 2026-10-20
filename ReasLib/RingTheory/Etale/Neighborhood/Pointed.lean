/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Etale.Neighborhood

@[expose] public section

/-!
# Residue-field projections of etale neighborhoods

An etale neighborhood already carries an equivalence from the base residue
field to the residue field at its selected point.  This leaf records its
inverse after the canonical map from the neighborhood algebra to that point's
residue field.  The result is an algebra homomorphism, rather than a global
algebra instance, so it can be used directly in tensor products and other
downstream constructions without creating competing scalar structures.
@stack 04GV
-/

universe u v

namespace PrimeSpectrum.EtaleNeighborhood

/-- The canonical map from an etale neighborhood algebra to the residue field
of its base point. -/
@[stacks 04GV "base residue-field projection of an etale neighborhood"]
noncomputable def toBaseResidueField {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood.{u, v} p) :
    U.carrier →ₐ[R] p.asIdeal.ResidueField :=
  U.residueFieldAlgEquiv.symm.toAlgHom.comp
    (IsScalarTower.toAlgHom R U.carrier U.point.asIdeal.ResidueField)

/-- The base residue-field projection restricts to the canonical map from the
base ring to its residue field. -/
@[stacks 04GV "base compatibility of an etale neighborhood residue projection"]
theorem toBaseResidueField_comp_algebraMap {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood.{u, v} p) :
    U.toBaseResidueField.comp (Algebra.ofId R U.carrier) =
      Algebra.ofId R p.asIdeal.ResidueField := sorry

/-- The kernel of the base residue-field projection is exactly the selected
point of the etale neighborhood. -/
@[stacks 04GV "kernel of the base residue-field projection"]
theorem ker_toBaseResidueField {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood.{u, v} p) :
    RingHom.ker U.toBaseResidueField.toRingHom = U.point.asIdeal := sorry

/-- The base residue-field projection is characterized by its scalar
compatibility and its kernel. -/
@[stacks 04GV "specification of the base residue-field projection"]
theorem toBaseResidueField_spec {R : Type u} [CommRing R]
    {p : PrimeSpectrum R} (U : EtaleNeighborhood.{u, v} p) :
    U.toBaseResidueField.comp (Algebra.ofId R U.carrier) =
        Algebra.ofId R p.asIdeal.ResidueField ∧
      RingHom.ker U.toBaseResidueField.toRingHom = U.point.asIdeal := sorry

end PrimeSpectrum.EtaleNeighborhood
