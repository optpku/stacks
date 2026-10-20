module

public import Mathlib.Algebra.Algebra.Tower
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Instances
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue

/-!
# Residue algebra maps of complete local algebras
-/

@[expose] public section

open IsLocalRing

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

noncomputable section

/-- The canonical residue map `R.carrier →ₐ[Λ] k` of a completed local algebra. -/
def residueFieldHom (R : CompleteLocalAlgCat Λ k) : R.carrier →ₐ[Λ] k :=
  R.residueFieldIso.toAlgHom.comp
    (IsScalarTower.toAlgHom Λ R.carrier (ResidueField R.carrier))

/-- `residueFieldHom` is the residue identification after the quotient map to the residue field. -/
theorem residueFieldHom_apply (R : CompleteLocalAlgCat Λ k) (x : R.carrier) :
    residueFieldHom R x =
      R.residueFieldIso (Ideal.Quotient.mk R.maximalIdeal x) := sorry

/-- The canonical map from a complete local algebra to its identified residue field is surjective. -/
theorem algebraMap_surjective (R : CompleteLocalAlgCat Λ k) :
    Function.Surjective (algebraMap R.carrier k) :=
  sorry

end

end CompleteLocalAlgCat
