module

public import Mathlib.Algebra.Algebra.Tower
public import stacks_project.Chap90.Definition_90_7_3_CompleteLocal

/-!
# Residue algebra structure on the identified residue field

A residue identification `ResidueField R.carrier ≃ₐ[Λ] k` makes `k` into an `R`-algebra,
so that `Derivation Λ R.carrier k` is the space of `Λ`-derivations from `R` into `k`.
-/

@[expose] public section

open IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- Residue-field identification of a complete local algebra as an `R`-algebra structure on `k`. -/
instance algebra_residue (R : CompleteLocalAlgCat Λ k) : Algebra R.carrier k :=
  (R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier)).toAlgebra

/-- The algebra map of `algebra_residue` is the residue identification after the residue-field
quotient map. -/
theorem algebra_residue_algebraMap (R : CompleteLocalAlgCat Λ k) :
    algebraMap R.carrier k = R.residueFieldIso.toAlgHom.toRingHom.comp (residue R.carrier) :=
  sorry

/-- The tower `Λ → R → k` for the residue identification of a complete local algebra. -/
instance isScalarTower_residue (R : CompleteLocalAlgCat Λ k) :
    IsScalarTower Λ R.carrier k := sorry

end

end CompleteLocalAlgCat
