/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing.Counterexample

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/-!
# Lemma 33.21.1 compatibility entry point

The completed-local-ring presentation API over a field is owned by
`ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteLocalRing`.
-/

/- Lemma 33.21.1 (1): the completed local ring at a point of a locally Noetherian
scheme over a field is a quotient of a finite-variable formal power series ring
over its residue field, compatibly with the residue-field map. -/
@[stacks 0C52]
#check (AlgebraicGeometry.exists_residueField_mvPowerSeries_quotient_ringEquiv_completedStalk :
  ∀ {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left]
    (x : X.left),
    ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x)))
      (e : (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
          (X.left.presheaf.stalk x)),
        (((AlgebraicGeometry.Scheme.completedStalkResidueFieldMap X.left x).comp
          e.toRingHom).comp
            (algebraMap (X.left.residueField x)
              (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I))) =
          RingHom.id (X.left.residueField x))

/- Lemma 33.21.1 (2): in general, a completed-stalk presentation need not be
compatible with the base-field algebra structure. -/
@[stacks 0C52]
#check (AlgebraicGeometry.SchemeOverField.exists_no_powerSeriesQuotientAlgEquiv_completedStalk :
  ∃ (k : Type u) (_ : Field k)
    (X : Over (Spec (CommRingCat.of k))) (_ : IsLocallyNoetherian X.left)
    (x : X.left),
    ¬ ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x))),
      Nonempty
        ((MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃ₐ[k]
          AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
            (X.left.presheaf.stalk x)))

/- Lemma 33.21.1 (3): if the residue field at the point is separable over the
base field, the presentation may be chosen as a base-field algebra
equivalence. -/
@[stacks 0C52]
#check (AlgebraicGeometry.SchemeOverField.exists_powerSeriesQuotientAlgEquiv_of_isSeparable :
  ∀ {k : Type u} [Field k]
    (X : Over (Spec (CommRingCat.of k))) [IsLocallyNoetherian X.left]
    (x : X.left),
    Algebra.IsSeparable k (X.left.residueField x) →
    ∃ (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) (X.left.residueField x)))
      (e : (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I) ≃ₐ[k]
        AdicCompletion (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x))
          (X.left.presheaf.stalk x)),
        (((AlgebraicGeometry.Scheme.completedStalkResidueFieldMap X.left x).comp
          e.toRingHom).comp
            (algebraMap (X.left.residueField x)
              (MvPowerSeries (Fin n) (X.left.residueField x) ⧸ I))) =
          RingHom.id (X.left.residueField x))
