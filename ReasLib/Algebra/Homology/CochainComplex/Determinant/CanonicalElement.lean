/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Determinant.Composition
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.CrossRefAttribute

/-!
# Canonical determinant elements of rank-zero two-term complexes

The canonical element is the restriction of the exterior-algebra map induced by the differential
to the determinant submodules in degrees `-1` and `0`.  Admissible maps preserve rank zero and
carry these elements through the covariant determinant equivalence.

@stack 0FJJ
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Module.Determinant

universe u

namespace CochainComplex.Determinant

variable {R : Type u} [CommRing R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- A two-term cochain complex has rank zero when its terms in degrees `-1` and `0` have the same
local rank at every prime of the base ring. -/
@[stacks 0FJJ "rank-zero two-term complex"]
def IsRankZero (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0] : Prop :=
  ∀ p : PrimeSpectrum R, Module.rankAtStalk (K.X (-1)) p = Module.rankAtStalk (K.X 0) p

/-- The differential of a rank-zero two-term complex carries determinant elements into the
determinant submodule in degree `0`. -/
theorem canonical_mem {K : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hK : IsRankZero K) (x : det[R](K.X (-1))) :
    ExteriorAlgebra.map (K.d (-1) 0).hom (x : ExteriorAlgebra R (K.X (-1))) ∈
      det[R](K.X 0) := sorry
-- Proof strategy: localize at each prime, use `hK` to identify the two local
-- ranks, and apply the top-exterior-power characterization of the determinant
-- submodule to the localized differential map.

/-- The canonical determinant element of a rank-zero two-term cochain complex. -/
@[stacks 0FJJ "canonical determinant element of a rank-zero two-term complex"]
def canonical (K : Cpx)
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hK : IsRankZero K) : line K :=
  LinearMap.codRestrict
    (det[R](K.X 0))
    ((ExteriorAlgebra.map (K.d (-1) 0).hom).toLinearMap.comp
      (Module.Determinant.ι R (K.X (-1))))
    (canonical_mem hK)

/-- Evaluation of the canonical determinant element is induced by the complex differential. -/
@[simp, stacks 0FJJ "canonical determinant element evaluation"]
theorem canonical_apply {K : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    (hK : IsRankZero K) (x : det[R](K.X (-1))) :
    ((canonical K hK x : det[R](K.X 0)) : ExteriorAlgebra R (K.X 0)) =
      ExteriorAlgebra.map (K.d (-1) 0).hom (x : ExteriorAlgebra R (K.X (-1))) := sorry
-- Proof strategy: unfold `canonical` and reduce the coercions through
-- `LinearMap.codRestrict`, `LinearMap.comp`, and `Module.Determinant.ι`.

/-- Rank zero pulls back along an admissible map of two-term cochain complexes. -/
@[stacks 0FJJ "rank zero under an admissible morphism"]
theorem IsRankZero.source {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a : K ⟶ L} (hL : IsRankZero L) (ha : IsAdmissible a) : IsRankZero K := sorry
-- Proof strategy: at each prime, use the two surjective component maps to write
-- the source ranks as kernel rank plus target rank.  Transport the kernel ranks
-- across the localized bijective `kernelDifferential`, then apply `hL`.

/-- The inverse determinant map carries the target canonical element to the source canonical
element. -/
theorem map_canonical {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a : K ⟶ L} (ha : IsAdmissible a) (hL : IsRankZero L) :
    map a ha (canonical L hL) = canonical K (hL.source ha) := sorry
-- Proof strategy: expand `map` and `canonical`, apply
-- `Module.Determinant.tensorIsoOfExact_spec` to both kernel rows, and use the
-- determinant map of `kernelDifferential`; verify the resulting equality on
-- exterior generators and extend across the determinant submodules.

/-- Lemma 15.123.1 (0FJJ): the determinant equivalence of an admissible map carries the canonical
element of the source rank-zero complex to the canonical element of the target. -/
@[stacks 0FJJ "Lemma 15.123.1: determinant maps preserve canonical elements"]
theorem equiv_canonical {K L : Cpx}
    [K.IsStrictlyGE (-1)] [K.IsStrictlyLE 0]
    [L.IsStrictlyGE (-1)] [L.IsStrictlyLE 0]
    [Module.Finite R (K.X (-1))] [Module.Projective R (K.X (-1))]
    [Module.Finite R (K.X 0)] [Module.Projective R (K.X 0)]
    [Module.Finite R (L.X (-1))] [Module.Projective R (L.X (-1))]
    [Module.Finite R (L.X 0)] [Module.Projective R (L.X 0)]
    {a : K ⟶ L} (ha : IsAdmissible a) (hL : IsRankZero L) :
    equiv a ha (canonical K (hL.source ha)) = canonical L hL := sorry
-- Proof strategy: rewrite the inverse of `equiv a ha` with
-- `equiv_symm_toLinearMap`, apply `map_canonical`, and cancel the linear
-- equivalence.

end CochainComplex.Determinant

end
