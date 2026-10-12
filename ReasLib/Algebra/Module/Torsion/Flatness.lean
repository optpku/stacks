/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.RingTheory.Flatness.LocallyFree.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness criteria for torsion-free modules

This leaf exposes torsion-freeness, rather than vanishing of the torsion submodule, on the public
side of the standard Bezout and Dedekind flatness criteria. It also packages the finite
locally-free consequence over a Dedekind domain.

@stack 0539
@stack 0AUW
-/

@[expose] public section

universe u v

namespace Module.Flat

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Lemma 15.22.10 (0539), in its reusable Bezout-domain form: flatness is equivalent to
torsion-freeness. -/
@[stacks 0539 "flatness iff torsion-freeness over a Bezout domain"]
theorem iff_isTorsionFree_of_isBezout [IsBezout R] [IsDomain R] :
    Flat R M ↔ IsTorsionFree R M := sorry
-- Proof strategy: combine `flat_iff_torsion_eq_bot_of_isBezout` with
-- `Submodule.isTorsionFree_iff_torsion_eq_bot`.

/-- Lemma 15.22.11 (1): over a Dedekind domain, flatness is equivalent to
torsion-freeness. -/
@[stacks 0AUW "(1) Dedekind flatness iff torsion-freeness"]
theorem iff_isTorsionFree_of_isDedekindDomain [IsDedekindDomain R] :
    Flat R M ↔ IsTorsionFree R M := sorry
-- Proof strategy: combine `IsDedekindDomain.flat_iff_torsion_eq_bot` with
-- `Submodule.isTorsionFree_iff_torsion_eq_bot`.

end Module.Flat

namespace Module.FiniteLocallyFree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Lemma 15.22.11 (2): a finite torsion-free module over a Dedekind domain is finite locally
free. This remains a theorem rather than an instance because `FiniteLocallyFree` already supplies
a `Module.Finite` instance in the opposite direction. -/
@[stacks 0AUW "(2) finite torsion-free modules are finite locally free"]
theorem of_finite_of_isTorsionFree_of_isDedekindDomain [IsDedekindDomain R]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    FiniteLocallyFree R M := sorry
-- Proof strategy: obtain flatness from `Module.Flat.iff_isTorsionFree_of_isDedekindDomain`, use
-- Noetherianity to construct `Module.FinitePresentation R M`, and apply
-- `Module.FiniteLocallyFree.of_finitePresentation_of_flat`.

end Module.FiniteLocallyFree
