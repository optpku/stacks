/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flatness.MittagLeffler.PowerSeries
public import ReasLib.RingTheory.Flatness.MittagLeffler.Projective

/-!
# Projectivity detected by power-series embeddings

This leaf specializes the universally-injective projectivity criterion to the canonical flat
Mittag-Leffler module of finite-variable formal power series over a Noetherian ring.
-/

@[expose] public section

universe u v

namespace LinearMap.UniversallyInjective

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {n : ℕ} {f : M →ₗ[R] MvPowerSeries (Fin n) R}

/-- Lemma 10.93.5, tag `05A1`: a universally injective map to a finite-variable power-series
module has projective source when the source is a direct sum of countably generated submodules. -/
@[stacks 05A1]
theorem projective_to_mvPowerSeries
    (hf : UniversallyInjective.{u, v, u, max u v} f)
    (hM : Module.IsDirectSumOfCountablyGenerated R M) :
    Module.Projective R M := sorry

end LinearMap.UniversallyInjective
