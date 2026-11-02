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
    algebraMap R.carrier k = R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier) := rfl

/-- The residue action of a complete local algebra on `k` agrees with its base algebra action. -/
instance isScalarTower_residue (R : CompleteLocalAlgCat Λ k) :
    IsScalarTower Λ R.carrier k := by
  apply IsScalarTower.of_algebraMap_eq
  intro scalar
  change algebraMap Λ k scalar =
    R.residueFieldIso (algebraMap Λ (ResidueField R.carrier) scalar)
  exact (R.residueFieldIso.commutes scalar).symm

/-- The canonical morphism from a complete local algebra to the identified residue field. -/
noncomputable def residueHom (R : CompleteLocalAlgCat Λ k) :
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k) :=
  Hom.of
    (R.residueFieldIso.toAlgHom.comp
      (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)))
    (by
      let hom := R.residueFieldIso.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier))
      letI : IsLocalHom hom.toRingHom :=
        IsLocalHom.of_surjective hom.toRingHom
          (R.residueFieldIso.surjective.comp (residue_surjective (R := R.carrier)))
      exact ⟨fun x hx => isUnit_of_map_unit hom.toRingHom x hx⟩)
    (by
      apply AlgHom.ext
      intro x
      obtain ⟨x, rfl⟩ := residue_surjective (R := R.carrier) x
      change
        ((Ideal.quotientEquivAlgOfEq Λ maximalIdeal_eq_bot).trans (AlgEquiv.quotientBot Λ k))
            (residue k (R.residueFieldIso (residue R.carrier x))) =
          R.residueFieldIso (residue R.carrier x)
      simp only [residue_def, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
        AlgEquiv.quotientBot_mk])

/-- The underlying algebra map of the canonical residue morphism is the residue quotient
followed by the chosen residue-field identification. -/
theorem residueHom_hom (R : CompleteLocalAlgCat Λ k) :
    (residueHom R).hom =
      R.residueFieldIso.toAlgHom.comp
        (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier)) := rfl

/-- Every morphism from a complete local algebra to the identified residue field is canonical. -/
theorem eq_residueHom (R : CompleteLocalAlgCat Λ k)
    (f : R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) :
    f = residueHom R := by
  have hom_eq : f.hom = (residueHom R).hom := by
    apply AlgHom.ext
    intro x
    have compat := DFunLike.congr_fun f.residue_compat (residue R.carrier x)
    change
      ((Ideal.quotientEquivAlgOfEq Λ maximalIdeal_eq_bot).trans (AlgEquiv.quotientBot Λ k))
          (residue k (f.hom x)) = R.residueFieldIso (residue R.carrier x) at compat
    change (f.hom x : k) = R.residueFieldIso (residue R.carrier x)
    simp only [residue_def, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      AlgEquiv.quotientBot_mk] at compat
    exact compat
  cases f with
  | mk hom hf =>
    cases hf with
    | mk localness compat =>
      cases hres : residueHom R with
      | mk hom' hf' =>
        cases hf' with
        | mk localness' compat' =>
          have hh : hom = hom' := by simpa only [hres, Hom.hom] using hom_eq
          cases hh
          rfl

/-- A complete local algebra has a unique morphism to the identified residue field. -/
noncomputable instance instUnique_hom_residue (R : CompleteLocalAlgCat Λ k) :
    Unique (R ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.residue Λ k)) where
  default := residueHom R
  uniq := eq_residueHom R

end

end CompleteLocalAlgCat
