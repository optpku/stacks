/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

noncomputable section

universe u

namespace Polynomial

variable (p : ℕ)

/-- The Artin–Schreier operator `℘ : k[X] →+ k[X]`, `f ↦ f ^ p - f`. -/
def artinSchreier (k : Type u) [CommRing k] [CharP k p] [Fact p.Prime] :
    Polynomial k →+ Polynomial k :=
  (frobenius (Polynomial k) p).toAddMonoidHom - AddMonoidHom.id (Polynomial k)

/-- The Artin–Schreier operator evaluates to `f ^ p - f`. -/
theorem artinSchreier_apply (k : Type u) [CommRing k] [CharP k p] [Fact p.Prime]
    (f : Polynomial k) :
    artinSchreier p k f = f ^ p - f := sorry

/-- Polynomials whose coefficients in degrees divisible by `p` vanish. These are the
standard additive representatives of the cokernel of `artinSchreier p`, i.e. sums
`∑_{p ∤ n} λ_n X ^ n`. -/
def pCoprimeDegree (k : Type u) [CommRing k] : AddSubgroup (Polynomial k) where
  carrier := {f | ∀ n, p ∣ n → f.coeff n = 0}
  add_mem' := sorry
  zero_mem' := sorry
  neg_mem' := sorry

/-- Membership in `pCoprimeDegree p k` is vanishing of coefficients in degrees
divisible by `p`. -/
theorem mem_pCoprimeDegree {k : Type u} [CommRing k] {f : Polynomial k} :
    f ∈ pCoprimeDegree p k ↔ ∀ n, p ∣ n → f.coeff n = 0 := sorry

/-- The cokernel of the Artin–Schreier operator on `k[X]`. -/
abbrev artinSchreierCoker (k : Type u) [CommRing k] [CharP k p] [Fact p.Prime] :=
  Polynomial k ⧸ (artinSchreier p k).range

/-- The map on Artin–Schreier cokernels induced by scalar extension `k → k'`. -/
def artinSchreierCokerMap (k k' : Type u) [CommRing k] [CommRing k']
    [CharP k p] [CharP k' p] [Fact p.Prime] [Algebra k k'] :
    artinSchreierCoker p k →+ artinSchreierCoker p k' :=
  QuotientAddGroup.map (artinSchreier p k).range (artinSchreier p k').range
    (mapRingHom (algebraMap k k')).toAddMonoidHom sorry

/-- Scalar extension of Artin–Schreier cokernels sends the class of `f` to the class
of `map (algebraMap k k') f`. -/
theorem artinSchreierCokerMap_apply (k k' : Type u) [CommRing k] [CommRing k']
    [CharP k p] [CharP k' p] [Fact p.Prime] [Algebra k k'] (f : Polynomial k) :
    artinSchreierCokerMap p k k'
        (QuotientAddGroup.mk' (artinSchreier p k).range f) =
      QuotientAddGroup.mk' (artinSchreier p k').range
        (map (algebraMap k k') f) := sorry

end Polynomial
