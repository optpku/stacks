/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.CohenRing
public import ReasLib.RingTheory.Completion.CohenStructure

@[expose] public section

/-!
# Power-series Presentations of Cohen Structures

@stack 032D

The core `Algebra.IsCohenStructure` package records the finite regular source
and its map to the target.  This leaf supplies the source-facing realization
of that source as a finite-variable power-series ring over a field or a Cohen
ring.
-/

universe u

open IsLocalRing

namespace IsCompleteLocalRing

/-- Lemma 10.160.11 (032D): a Noetherian complete local domain contains a finite regular
complete-local subring inducing an isomorphism on residue fields, and that subring is a
finite-variable power-series ring over either its residue field or a Cohen ring. -/
@[stacks 032D "power-series Cohen subring"]
theorem exists_powerSeries_cohenSubring
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsCompleteLocalRing R] :
    ∃ (R₀ : Subring R) (_ : IsCompleteLocalRing R₀) (_ : IsRegularLocalRing R₀)
      (_ : IsLocalHom (R₀.subtype : R₀ →+* R))
      (_ : Function.Bijective (ResidueField.map (R₀.subtype : R₀ →+* R)))
      (_ : Module.Finite R₀ R),
      ∃ d : ℕ,
        Nonempty (MvPowerSeries (Fin d) (ResidueField R₀) ≃+* R₀) ∨
        ∃ (Λ : Type u) (_ : CommRing Λ) (_ : IsCohenRing Λ),
          Nonempty (MvPowerSeries (Fin d) Λ ≃+* R₀) := sorry

end IsCompleteLocalRing
