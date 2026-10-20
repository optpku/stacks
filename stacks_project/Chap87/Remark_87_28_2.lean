module

import StacksCheckRecall
public import ReasLib.RingTheory.AdicCompletion.Polynomial

/-!
Canonical stage algebra maps and unique compatible lifts identify the polynomial completion
with the inverse limit defining restricted power series. The limit topology is always
complete; no unconditional completeness of the extended-ideal adic topology is asserted.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] (r : ℕ) (I : Ideal A) [IsAdicComplete I A]

/- Remark 87.28.2 (1): over an `I`-adically complete ring, canonical stage algebra maps
and unique compatible lifts identify the polynomial completion with restricted power series. -/
@[stacks 0AL0] #check (IAdicRestrictedPowerSeries.compatibleStages_liftUnique (Fin r) I :
  ∀ family : (n : ℕ) → MvPolynomial (Fin r) (A ⧸ I ^ n),
    IAdicRestrictedPowerSeries.CompatibleStages (Fin r) I family →
      ∃! series : IAdicRestrictedPowerSeries (Fin r) I,
        ∀ n, IAdicRestrictedPowerSeries.stageHom (Fin r) I n series = family n)

/- Remark 87.28.2 (2): the discrete-stage limit topology is always complete, whereas
the extended-ideal adic topology on the polynomial completion need not be. -/
@[stacks 0AL0] #check (AdicCompletion.completeSpace_limitUniformSpace
  (I.map (algebraMap A (MvPolynomial (Fin r) A))) :
  @CompleteSpace (IAdicRestrictedPowerSeries (Fin r) I)
    (AdicCompletion.limitUniformSpace (I.map (algebraMap A (MvPolynomial (Fin r) A)))))

/- Remark 87.28.2 (3): if `I` is finitely generated, restricted power series and the
polynomial completion agree as topological rings, by Algebra, Lemma 10.96.3. -/
@[stacks 0AL0] #check (IAdicRestrictedPowerSeries.limitTopology_eq_adic (Fin r) I :
  I.FG → IAdicRestrictedPowerSeries.limitTopology (Fin r) I =
    (IAdicRestrictedPowerSeries.extendedIdeal (Fin r) I).adicTopology)
