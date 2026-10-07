module

public import Mathlib.Data.Int.Range
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.DeterminantalIdeal
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise

/-!
# Alternating ranks for integer eta presentations

This file owns the finite alternating-rank correction attached to a bounded-above finite-free
cochain complex.  It is separated from derived-category invariance so numerical computations and
strict-isomorphism transport can be reused without importing derived categories.
@stack 0GSS
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int.DeterminantalIdeal

variable {A : Type u} [CommRing A]

/-- The alternating sum of term ranks from degree `i` through degree `b`, normalized to have
positive sign in degree `i`.  The definition has no proof parameters; finite freeness is imposed
only by results that use its rank interpretation. -/
@[stacks 0GSS "alternating rank correction for eta determinantal ideals"]
def alternatingRank (K : CochainComplex (ModuleCat.{v} A) ℤ) (i b : ℤ) : ℤ :=
  ((Int.range i (b + 1)).map fun j ↦
    (-1 : ℤ) ^ Int.toNat (j - i) * (Module.finrank A (K.X j) : ℤ)).sum

/-- A strict isomorphism of termwise finite-free complexes preserves every truncated alternating
rank. -/
theorem alternatingRank_eq_of_iso
    {K L : CochainComplex (ModuleCat.{v} A) ℤ}
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree]
    (e : K ≅ L) (i b : ℤ) :
    alternatingRank K i b = alternatingRank L i b := sorry

/-- Alternating rank is additive under biproducts of termwise finite-free complexes. -/
theorem alternatingRank_biprod
    (K L : CochainComplex (ModuleCat.{v} A) ℤ)
    [K.IsTermwiseFiniteFree] [L.IsTermwiseFiniteFree] (i b : ℤ) :
    alternatingRank (K ⊞ L) i b = alternatingRank K i b + alternatingRank L i b := sorry

end CochainComplex.BerthelotOgus.Int.DeterminantalIdeal
