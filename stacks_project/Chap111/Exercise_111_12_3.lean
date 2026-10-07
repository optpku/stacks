module

public import ReasLib.RingTheory.Depth.TorsionFree
public import ReasLib.RingTheory.PowerSeries.Depth
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v

open IsLocalRing
open scoped ENat

/- Exercise 111.12.3 (1): for a local Noetherian domain with nonzero maximal
ideal, a finite torsion-free module has depth at least one. The retained
nonzero-maximal-ideal condition excludes the field counterexample omitted by the
prose. -/
@[stacks 0CS3] #check
  (Module.IsTorsionFree.moduleDepth_ge_one :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [IsDomain R]
      [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
      [Module.IsTorsionFree R M] (h_maximalIdeal_ne_bot : maximalIdeal R ≠ ⊥),
      (1 : ℕ∞) ≤ moduleDepth R M)

/- Exercise 111.12.3 (2): the self-module of a one-variable power-series ring
over a field has depth exactly one. -/
@[stacks 0CS3] #check
  (PowerSeries.moduleDepth_self_eq_one :
    ∀ (k : Type u) [Field k],
      moduleDepth (PowerSeries k) (PowerSeries k) = 1)
