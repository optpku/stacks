/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.PowerSeries
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.26.1: if `(A, m)` is a Noetherian local ring of depth at least `2`,
`B = A[[x₁, …, x_d]]` with `d ≥ 1`, `Y = Spec B` and `Y₀ = V(x₁, …, x_d)`, then for
any open `V ⊂ Y` with `V ∩ Y₀` equal to `Y₀` minus the closed point `m_B`, restriction
`FÉt_V ⟶ FÉt_{V₀}` is fully faithful. -/
@[stacks 0EY9] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_fullyFaithful_of_powerSeriesDepth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hdepth : (2 : ℕ∞) ≤ moduleDepth A A) {d : ℕ} (hd : 0 < d)
    (V : (Spec (CommRingCat.of (MvPowerSeries (Fin d) A))).Opens)
    (hV :
      let i := Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
      i ⁻¹ᵁ V = PuncturedSpectrum.puncturedOpen A),
    let i := Spec.map (CommRingCat.ofHom
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) A →+* A))
    Nonempty (finiteEtaleBaseChange (pullback.fst V.ι i)).FullyFaithful)

end AlgebraicGeometry.Scheme
