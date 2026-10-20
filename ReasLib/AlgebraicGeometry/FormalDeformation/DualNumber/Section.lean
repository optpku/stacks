/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# The section of the dual-number projection

The constant-coefficient inclusion splits the projection from the dual numbers to the
residue-field object in the category of Artinian local algebras.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The constant-coefficient inclusion into the dual numbers is a local homomorphism. -/
instance residueInclusion_isLocalHom :
    IsLocalHom ((inlAlgHom k k k).restrictScalars Λ) where
  map_nonunit scalar h_unit :=
    IsUnit.of_map ((inlAlgHom k k k).restrictScalars Λ).toRingHom scalar h_unit

/-- The constant-coefficient inclusion preserves the chosen residue identifications. -/
theorem residueInclusion_residue_compat :
    residueCompat (A := residue Λ k) (B := dualNumber Λ k)
        ((inlAlgHom k k k).restrictScalars Λ) (residueInclusion_isLocalHom Λ k) =
      residueIsoHom (residue Λ k) := sorry

/-- The constant-coefficient inclusion from the residue-field object to the dual numbers. -/
def residueToDualNumber : residue Λ k ⟶ dualNumber Λ k :=
  Hom.of ((inlAlgHom k k k).restrictScalars Λ)
    (residueInclusion_isLocalHom Λ k) (residueInclusion_residue_compat Λ k)

/-- The underlying algebra map of the residue inclusion is the constant-coefficient map. -/
theorem residueToDualNumber_hom :
    (residueToDualNumber Λ k).hom = (inlAlgHom k k k).restrictScalars Λ := rfl

/-- The constant-coefficient inclusion followed by the coefficient projection is the identity. -/
theorem residueToDualNumber_comp_dualNumberToResidue :
    residueToDualNumber Λ k ≫ dualNumberToResidue Λ k = 𝟙 (residue Λ k) := rfl

/-- The residue inclusion into the dual numbers is a local homomorphism. -/
instance residueToDualNumber_isLocalHom :
    IsLocalHom (residueToDualNumber Λ k).hom := residueInclusion_isLocalHom Λ k

/-- The residue inclusion into the dual numbers preserves the residue identifications. -/
theorem residueToDualNumber_residue_compat :
    residueCompat (residueToDualNumber Λ k).hom (residueToDualNumber Λ k).isLocalHom =
      residueIsoHom (residue Λ k) := (residueToDualNumber Λ k).residue_compat

end ArtinianLocalAlgCat
