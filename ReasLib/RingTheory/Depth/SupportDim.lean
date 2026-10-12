/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Regular
public import ReasLib.RingTheory.Depth

/-!
# Depth and Support Dimension

@stack 00LK
@stack 0AUJ

This leaf owns the comparison between module depth and support dimension and
the resulting finiteness criterion for ideal depth.
-/

@[expose] public section

open scoped ENat

universe u v

namespace Module

/-- A prime in the support of a module gives an upper bound on the dimension of its quotient. -/
@[stacks 00LK "support-dimension quotient upper bound"]
theorem quotientDim_le_supportDim_of_mem
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) :
    ringKrullDim (R ⧸ p.asIdeal) ≤ Module.supportDim R M := sorry

/-- Lemma 10.72.3, tag `00LK`: the local depth of a nonzero finite module is
bounded by the dimension of its support. -/
@[stacks 00LK]
theorem depth_le_supportDim {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    .some (moduleDepth R M) ≤ supportDim R M := sorry

end Module

/-- Deprecated compatibility spelling for `Module.depth_le_supportDim`. -/
@[deprecated Module.depth_le_supportDim (since := "2026-08-04")]
theorem depth_le_supportDim {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Nontrivial M] :
    .some (moduleDepth R M) ≤ Module.supportDim R M := sorry

namespace Ideal

/-- Lemma 10.72.4, tag `0AUJ`: the depth of a finite module with respect to
an ideal not generating the whole module is finite. -/
@[stacks 0AUJ]
theorem depth_lt_top_of_smul_top_ne_top {R : Type u} [CommRing R]
    [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R)
    (hIM : I • (⊤ : Submodule R M) ≠ ⊤) :
    I.depth M < ⊤ := sorry

end Ideal
