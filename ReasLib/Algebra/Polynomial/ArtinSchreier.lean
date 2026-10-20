module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

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

/-- The additive subgroup of polynomials whose coefficients in every degree divisible
by `p` vanish, including the constant coefficient. -/
def pCoprimeDegree (k : Type u) [CommRing k] : AddSubgroup (Polynomial k) where
  carrier := {f | ∀ n, p ∣ n → f.coeff n = 0}
  add_mem' := by
    intro f g hf hg n hn
    simp only [coeff_add, hf n hn, hg n hn, add_zero]
  zero_mem' := by
    intro n hn
    exact coeff_zero n
  neg_mem' := by
    intro f hf n hn
    simp only [coeff_neg, hf n hn, neg_zero]

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
    (mapRingHom (algebraMap k k')).toAddMonoidHom (by
      intro f hf
      obtain ⟨g, rfl⟩ := hf
      refine ⟨map (algebraMap k k') g, ?_⟩
      change (map (algebraMap k k') g) ^ p - map (algebraMap k k') g =
        map (algebraMap k k') (g ^ p - g)
      simp only [Polynomial.map_sub, Polynomial.map_pow])

/-- Scalar extension of Artin–Schreier cokernels sends the class of `f` to the class
of `map (algebraMap k k') f`. -/
theorem artinSchreierCokerMap_apply (k k' : Type u) [CommRing k] [CommRing k']
    [CharP k p] [CharP k' p] [Fact p.Prime] [Algebra k k'] (f : Polynomial k) :
    artinSchreierCokerMap p k k'
        (QuotientAddGroup.mk' (artinSchreier p k).range f) =
      QuotientAddGroup.mk' (artinSchreier p k').range
        (map (algebraMap k k') f) := sorry

/-- Over an algebraically closed field of prime characteristic `p`, each class in the
Artin–Schreier cokernel has a unique polynomial representative with coefficients
vanishing in degrees divisible by `p`. -/
theorem pCoprimeDegree_represents_coker
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Function.Bijective
      ((QuotientAddGroup.mk' (artinSchreier p k).range).comp
        (pCoprimeDegree p k).subtype) := sorry

end Polynomial
