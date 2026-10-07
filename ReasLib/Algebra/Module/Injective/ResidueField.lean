module

public import ReasLib.Algebra.Module.Injective.Hull
public import ReasLib.Algebra.Module.IdealPower.Predicate
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

universe u v w

/-- A power-torsion module over a local ring embeds into a finite product of copies of
an injective hull of the residue field when its maximal-ideal socle has finite dimension. -/
theorem Module.exists_injective_to_pi_of_isIdealPowerTorsion
    (R : Type u) (E : Type v) (M : Type w) [CommRing R] [IsLocalRing R]
    [AddCommGroup E] [Module R E] [Module.Injective R E]
    [AddCommGroup M] [Module R M]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (hι : ι.IsInjectiveHull)
    (hM : Module.IsIdealPowerTorsion (IsLocalRing.maximalIdeal R) M) (n : ℕ)
    (hsocle : Nonempty
      ((IsLocalRing.maximalIdeal R).powerAnnihilatedSubmodule M 1 ≃ₗ[R]
        (Fin n → IsLocalRing.ResidueField R))) :
    ∃ f : M →ₗ[R] (Fin n → E), Function.Injective f := sorry

/-- The maximal-ideal torsion submodule of a module over a local ring is a module over
the residue field. -/
instance Submodule.instModuleResidueFieldTorsionByMaximalIdeal
    (R : Type u) (M : Type w) [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] :
    Module (IsLocalRing.ResidueField R)
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)) :=
  inferInstanceAs <| Module (R ⧸ IsLocalRing.maximalIdeal R)
    (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R))

noncomputable section

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The residue field acts on the space of linear maps from the residue field to the ring
by precomposition with multiplication on the domain. -/
instance instModuleResidueFieldLinearMapResidueFieldSelf :
    Module (ResidueField A) (ResidueField A →ₗ[A] A) where
  smul c f :=
    { toFun := fun x ↦ f (c * x)
      map_add' := sorry
      map_smul' := sorry }
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Scalar multiplication on the residue-field dual evaluates by precomposition with
multiplication: `(c • f) x = f (c * x)`. -/
theorem smul_linearMap_residueField_self_apply
    (c : ResidueField A) (f : ResidueField A →ₗ[A] A) (x : ResidueField A) :
    (c • f) x = f (c * x) := sorry

/-- The residue-field dual of a self-injective Artinian local ring is finite-dimensional
over its residue field. -/
instance instFiniteDimensionalLinearMapResidueFieldSelf
    [IsArtinianRing A] [Module.Injective A A] :
    FiniteDimensional (ResidueField A) (ResidueField A →ₗ[A] A) := sorry

/-- The residue-field dual of a self-injective Artinian local ring has dimension one
over its residue field. -/
theorem finrank_linearMap_residueField_self_eq_one
    [IsArtinianRing A] [Module.Injective A A] :
    Module.finrank (ResidueField A) (ResidueField A →ₗ[A] A) = 1 := sorry

end IsLocalRing
