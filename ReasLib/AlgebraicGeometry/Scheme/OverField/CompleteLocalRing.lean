module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.LocalRing.Completion
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local

/-!
# Completed local rings of schemes over a field

This leaf provides coefficient-field presentations of completed local rings
for locally Noetherian schemes over a field.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]
variable (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left]

/-- The completed local ring at a point of a locally Noetherian scheme over a
field is a quotient of a finite-variable formal power series ring over its
residue field, compatibly with the residue-field map. -/
@[stacks 0C52, stacks 0C53]
theorem exists_residueField_mvPowerSeries_quotient_ringEquiv_completedStalk
    (x : X.left) :
    ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x)))
      (e : (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
          (X.left.presheaf.stalk x)),
        (((Scheme.completedStalkResidueFieldMap X.left x).comp e.toRingHom).comp
            (algebraMap (X.left.residueField x)
              (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I))) =
          RingHom.id (X.left.residueField x) := sorry

namespace SchemeOverField

/-- If the residue field at a point is separable over the base field, the
completed local ring has a compatible presentation as a quotient of a
finite-variable formal power series ring by a base-field algebra equivalence. -/
@[stacks 0C52]
theorem exists_powerSeriesQuotientAlgEquiv_of_isSeparable
    (x : X.left)
    (hsep : Algebra.IsSeparable k (X.left.residueField x)) :
    ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x)))
      (e : (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
          (X.left.presheaf.stalk x)),
        (((Scheme.completedStalkResidueFieldMap X.left x).comp e.toRingHom).comp
            (algebraMap (X.left.residueField x)
              (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I))) =
          RingHom.id (X.left.residueField x) := sorry

end SchemeOverField

end AlgebraicGeometry
