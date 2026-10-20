/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Logic.Unique
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Inclusion
public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Residue
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal

/-!
# Residue scalar structures of complete local algebras

The stored residue identification makes the residue field into an algebra over the
complete local algebra, compatibly with the base algebra structure.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

/-- The carrier of a complete local algebra has its stored base algebra structure. -/
instance instAlgebraCarrier (R : CompleteLocalAlgCat Λ k) : Algebra Λ R.carrier :=
  R.algebra

/-- The carrier of a complete local algebra has its stored local-ring structure. -/
instance instIsLocalRingCarrier (R : CompleteLocalAlgCat Λ k) : IsLocalRing R.carrier :=
  R.isLocalRing

noncomputable section

/-- A residue-field identification makes `k` an algebra over the complete local algebra. -/
instance algebra_residue (R : CompleteLocalAlgCat Λ k) : Algebra R.carrier k :=
  (R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier)).toAlgebra

/-- The residue algebra map is the residue quotient followed by the residue identification. -/
theorem algebra_residue_algebraMap (R : CompleteLocalAlgCat Λ k) :
    algebraMap R.carrier k = R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier) := sorry

/-- The residue action of a complete local algebra on `k` agrees with its base algebra action. -/
instance isScalarTower_residue (R : CompleteLocalAlgCat Λ k) :
    IsScalarTower Λ R.carrier k := sorry

/-- The canonical morphism from a complete local algebra to the identified residue field. -/
noncomputable def residueHom (R : CompleteLocalAlgCat Λ k) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k) :=
  Hom.of
    (R.residueFieldIso.toAlgHom.comp
      (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)))
    sorry sorry

/-- The underlying algebra map of the canonical residue morphism is the residue quotient
followed by the chosen residue-field identification. -/
theorem residueHom_hom (R : CompleteLocalAlgCat Λ k) :
    (residueHom R).hom =
      R.residueFieldIso.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)) := sorry

/-- Every morphism from a complete local algebra to the identified residue field is canonical. -/
theorem eq_residueHom (R : CompleteLocalAlgCat Λ k)
    (f : R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) :
    f = residueHom R := sorry

/-- A complete local algebra has a unique morphism to the identified residue field. -/
noncomputable instance instUnique_hom_residue (R : CompleteLocalAlgCat Λ k) :
    Unique (R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) where
  default := residueHom R
  uniq := sorry

end

end CompleteLocalAlgCat
