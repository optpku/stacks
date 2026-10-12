/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import ReasLib.RingTheory.Sequence.QuasiRegular.Equiv

/-!
# Flat Base Change of Quasi-Regular Sequences

Quasi-regular sequences are preserved by flat base change, first for an arbitrary owner-level
`IsBaseChange` map and then for the canonical tensor-product model.
-/

@[expose] public section

open scoped TensorProduct

universe u v w x

namespace RingTheory.Sequence.IsQuasiRegular

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {S : Type w} [CommRing S] [Algebra R S] [Module.Flat R S]
variable {N : Type x} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Quasi-regularity is preserved by a flat owner-level base-change map. -/
@[stacks 065L "owner-level base change"]
theorem of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {rs : List R}
    (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular N (rs.map (algebraMap R S)) := sorry

/-- Lemma 10.69.3, tag `065L`: a quasi-regular sequence remains quasi-regular after canonical
flat scalar extension. -/
@[stacks 065L]
theorem of_flat {rs : List R} (hqr : IsQuasiRegular M rs) :
    IsQuasiRegular (S ⊗[R] M) (rs.map (algebraMap R S)) := sorry

end RingTheory.Sequence.IsQuasiRegular
