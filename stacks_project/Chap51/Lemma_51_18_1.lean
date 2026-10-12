/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPowerSeries.TorsionModule
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 51.18.1: Let `k` be a field of characteristic zero, let `d ≥ 1`, and put
`A = MvPowerSeries (Fin d) k`. If the `A`-module `M` is power torsion for the maximal
ideal and has additive operators satisfying the Leibniz rule for every formal partial
derivative, then `M` is isomorphic to a direct sum of copies of an injective hull `E`
of the residue field. -/
@[stacks 0EC2] #check (Module.equivDirectSumInjectiveHull_of_partialDerivations :
  ∀ (k : Type u) [Field k] [CharZero k] (d : ℕ) (hd : 0 < d)
    (M : Type v) (E : Type w)
    [AddCommGroup M] [Module (MvPowerSeries (Fin d) k) M]
    [AddCommGroup E] [Module (MvPowerSeries (Fin d) k) E]
    [Module.Injective (MvPowerSeries (Fin d) k) E]
    (ι : IsLocalRing.ResidueField (MvPowerSeries (Fin d) k) →ₗ[MvPowerSeries (Fin d) k]
      E)
    (hι : ι.IsInjectiveHull) (D : Fin d → M →+ M)
    (hD : ∀ (i : Fin d) (f : MvPowerSeries (Fin d) k) (z : M),
      D i (f • z) = MvPowerSeries.partialDeriv i f • z + f • D i z)
    (hM : Module.IsIdealPowerTorsion
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) k)) M),
    ∃ J : Type v,
      Nonempty (M ≃ₗ[MvPowerSeries (Fin d) k] DirectSum J (fun _ ↦ E)))
