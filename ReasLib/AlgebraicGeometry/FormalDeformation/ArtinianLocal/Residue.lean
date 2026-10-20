/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.Instances

/-!
# The residue-field object of the Artinian local algebra category
-/

@[expose] public section

open IsLocalRing

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- The residue field `k`, viewed as an object of `ArtinianLocalAlgCat Λ k`. -/
def residue : ArtinianLocalAlgCat Λ k :=
  of k ((Ideal.quotientEquivAlgOfEq Λ maximalIdeal_eq_bot).trans (AlgEquiv.quotientBot Λ k))

/-- The bundled residue object has carrier `k`. -/
theorem residue_carrier : (residue Λ k).carrier = k := sorry

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The algebra map from an Artinian local algebra to its identified residue field. -/
noncomputable def toResidueHom (A : ArtinianLocalAlgCat Λ k) :
    A.carrier →ₐ[Λ] (residue Λ k).carrier :=
  A.residueFieldIso.toAlgHom.comp (Ideal.Quotient.mkₐ Λ (maximalIdeal A.carrier))

/-- The residue map to the identified residue field is local. -/
theorem toResidueHom_isLocalHom (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (toResidueHom A) := sorry

/-- The residue map agrees with the chosen residue-field identification. -/
theorem toResidueHom_residue_compat (A : ArtinianLocalAlgCat Λ k) :
    residueCompat (toResidueHom A) (toResidueHom_isLocalHom A) = residueIsoHom A := sorry

/-- The canonical morphism from an Artinian local algebra to its residue object. -/
noncomputable def toResidue (A : ArtinianLocalAlgCat Λ k) : A ⟶ residue Λ k :=
  Hom.of (toResidueHom A) (toResidueHom_isLocalHom A) (toResidueHom_residue_compat A)

/-- The underlying algebra map of the canonical residue morphism. -/
theorem toResidue_hom (A : ArtinianLocalAlgCat Λ k) :
    (toResidue A).hom = toResidueHom A := rfl

/-- The canonical residue morphism is local and residue-compatible. -/
theorem toResidue_spec (A : ArtinianLocalAlgCat Λ k) :
    IsLocalHom (toResidue A).hom ∧
      residueCompat (toResidue A).hom (toResidue A).isLocalHom = residueIsoHom A := by
  exact ⟨toResidueHom_isLocalHom A, Hom.residue_compat (toResidue A)⟩

/-- The algebra structure on the identified residue field induced by the canonical residue map. -/
@[reducible] noncomputable def residueAlgebra (A : ArtinianLocalAlgCat Λ k) :
    Algebra A.carrier k :=
  (toResidueHom A).toRingHom.toAlgebra

/-- The identified residue field carries its canonical algebra structure over the local algebra. -/
noncomputable instance instAlgebraResidue (A : ArtinianLocalAlgCat Λ k) :
    Algebra A.carrier k :=
  residueAlgebra A

/-- The algebra map to the identified residue field is the canonical residue homomorphism. -/
theorem residueAlgebra_algebraMap (A : ArtinianLocalAlgCat Λ k) :
    algebraMap A.carrier k = (toResidueHom A).toRingHom := rfl

/-- The canonical residue algebra structure is compatible with the base algebra structure. -/
instance instIsScalarTowerResidue (A : ArtinianLocalAlgCat Λ k) :
    IsScalarTower Λ A.carrier k := sorry

/-- The canonical map from a local algebra to its identified residue field is surjective. -/
theorem toResidueHom_surjective (A : ArtinianLocalAlgCat Λ k) :
    Function.Surjective (toResidueHom A) := sorry

/-- The kernel of the canonical residue homomorphism is the maximal ideal. -/
theorem ker_toResidueHom (A : ArtinianLocalAlgCat Λ k) :
    RingHom.ker (toResidueHom A).toRingHom = IsLocalRing.maximalIdeal A.carrier := sorry

end ArtinianLocalAlgCat
