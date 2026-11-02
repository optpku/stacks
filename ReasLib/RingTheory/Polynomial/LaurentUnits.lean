/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Int.Units
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Polynomial.Laurent

@[expose] public section

noncomputable section

open scoped LaurentPolynomial

namespace LaurentPolynomial

/-- The monomial unit `C u * T n` in `(ℤ[T;T⁻¹])ˣ`. -/
def monomialUnit (u : ℤˣ) (n : ℤ) : (ℤ[T;T⁻¹])ˣ :=
  Units.map C.toMonoidHom u * unitOfInvertible (T n)

/-- The underlying Laurent polynomial of `monomialUnit u n` is `C u * T n`. -/
theorem monomialUnit_coe (u : ℤˣ) (n : ℤ) :
    (monomialUnit u n).val = C (u : ℤ) * T n :=
  rfl

/-- Monomial units `± T n` are uniquely determined by the coefficient unit and exponent. -/
theorem monomialUnit_eq_iff (u v : ℤˣ) (m n : ℤ) :
    monomialUnit u n = monomialUnit v m ↔ u = v ∧ n = m := by
  constructor
  · intro h
    have hval := congrArg Units.val h
    rw [monomialUnit_coe, monomialUnit_coe] at hval
    have hn : n = m := WithBot.coe_injective <| by
      simpa only [degree_C_mul_T n (u : ℤ) u.ne_zero,
        degree_C_mul_T m (v : ℤ) v.ne_zero] using congrArg degree hval
    subst m
    refine ⟨Units.ext ?_, rfl⟩
    simpa only [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_eq_same] using congrArg (fun f : ℤ[T;T⁻¹] => f.coeff n) hval
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The group homomorphism sending `(u, n)` to the monomial unit `C u * T n.toAdd`. -/
def unitsMulHom : ℤˣ × Multiplicative ℤ →* (ℤ[T;T⁻¹])ˣ where
  toFun p := monomialUnit p.fst p.snd.toAdd
  map_one' := by
    apply Units.ext
    simp [monomialUnit_coe]
  map_mul' p q := by
    apply Units.ext
    change (monomialUnit (p * q).fst (p * q).snd.toAdd).val =
      (monomialUnit p.fst p.snd.toAdd).val * (monomialUnit q.fst q.snd.toAdd).val
    simp only [monomialUnit_coe, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, Units.val_mul, map_mul, T_add]
    ac_rfl

/-- `unitsMulHom` evaluates as `monomialUnit` on a pair. -/
theorem unitsMulHom_apply (u : ℤˣ) (n : Multiplicative ℤ) :
    unitsMulHom (u, n) = monomialUnit u n.toAdd :=
  rfl

private theorem coeff_mul_of_extremal_exponents {R : Type*} [Semiring R] {f g : R[T;T⁻¹]}
    {m n : ℤ} (d : ℤ → ℤ) (hd : Function.Injective d)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hm : ∀ a ∈ f.coeff.support, d a ≤ d m)
    (hn : ∀ b ∈ g.coeff.support, d b ≤ d n) :
    (f * g).coeff (m + n) = f.coeff m * g.coeff n := by
  classical
  simp_rw [AddMonoidAlgebra.coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single m, Finset.sum_eq_single n, if_pos rfl]
  · exact fun b _ hne => if_neg (fun h => hne (add_left_cancel h))
  · intro h
    rw [if_pos rfl, Finsupp.notMem_support_iff.mp h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun b hb => if_neg (fun he => ?_))
    have h := congrArg d he
    rw [hadd, hadd] at h
    have ha' : d a ≠ d m := fun e => hne (hd e)
    have hle := hm a ha
    have hle' := hn b hb
    omega
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr (fun _ => ?_))
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

/-- Every Laurent polynomial unit over a commutative semiring without zero divisors is a monomial. -/
theorem exists_eq_C_mul_T_of_isUnit {R : Type*} [CommSemiring R]
    [NoZeroDivisors R] {p : R[T;T⁻¹]} (hp : IsUnit p) :
    ∃ (u : Rˣ) (n : ℤ), p = C (u : R) * T n := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨1, 0, Subsingleton.elim _ _⟩
  rcases hp with ⟨x, rfl⟩
  let f : R[T;T⁻¹] := x.val
  let g : R[T;T⁻¹] := (x⁻¹).val
  have hf : f ≠ 0 := x.ne_zero
  have hg : g ≠ 0 := (x⁻¹).ne_zero
  have hfg : f * g = 1 := x.mul_inv
  have hf' : f.coeff.support.Nonempty := by
    simpa only [Finsupp.support_nonempty_iff, ne_eq, AddMonoidAlgebra.coeff_eq_zero] using hf
  have hg' : g.coeff.support.Nonempty := by
    simpa only [Finsupp.support_nonempty_iff, ne_eq, AddMonoidAlgebra.coeff_eq_zero] using hg
  obtain ⟨m, hm, hfm⟩ := Finset.exists_max_image f.coeff.support (fun i : ℤ => i) hf'
  obtain ⟨n, hn, hgn⟩ := Finset.exists_max_image g.coeff.support (fun i : ℤ => i) hg'
  obtain ⟨k, hk, hfk⟩ := Finset.exists_max_image f.coeff.support (fun i : ℤ => -i) hf'
  obtain ⟨l, hl, hgl⟩ := Finset.exists_max_image g.coeff.support (fun i : ℤ => -i) hg'
  have hexponent (d : ℤ → ℤ) (hd : Function.Injective d)
      (hadd : ∀ a b, d (a + b) = d a + d b) {a b : ℤ}
      (ha : a ∈ f.coeff.support) (hb : b ∈ g.coeff.support)
      (hfa : ∀ i ∈ f.coeff.support, d i ≤ d a)
      (hgb : ∀ i ∈ g.coeff.support, d i ≤ d b) : a + b = 0 := by
    have hc : (f * g).coeff (a + b) ≠ 0 := by
      rw [coeff_mul_of_extremal_exponents d hd hadd hfa hgb]
      exact mul_ne_zero (Finsupp.mem_support_iff.mp ha) (Finsupp.mem_support_iff.mp hb)
    have hs := Finsupp.mem_support_iff.mpr hc
    rw [hfg] at hs
    change a + b ∈ (Finsupp.single 0 (1 : R)).support at hs
    exact Finset.mem_singleton.mp (Finsupp.support_single_subset hs)
  have hmax : m + n = 0 :=
    hexponent (fun i => i) Function.injective_id (fun _ _ => rfl) hm hn hfm hgn
  have hmin : k + l = 0 :=
    hexponent (fun i => -i) neg_injective (by intro a b; omega) hk hl hfk hgl
  have hsupport : ∀ i ∈ f.coeff.support, i = m := by
    intro i hi
    have hu : i ≤ m := hfm i hi
    have hv : -i ≤ -k := hfk i hi
    have hkm : k ≤ m := hfm k hk
    have hln : l ≤ n := hgn l hl
    omega
  have hmono : f = C (f.coeff m) * T m := by
    rw [← single_eq_C_mul_T]
    apply LaurentPolynomial.ext
    intro i
    by_cases hi : i = m
    · subst i
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    · have hz : f.coeff i = 0 := Finsupp.notMem_support_iff.mp (fun h => hi (hsupport i h))
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (Ne.symm hi), hz]
  have hu : IsUnit (f.coeff m) := by
    have h := x.isUnit.map (eval₂ (RingHom.id R) 1)
    change IsUnit (eval₂ (RingHom.id R) 1 f) at h
    rw [hmono] at h
    simpa using h
  obtain ⟨u, hu⟩ := hu
  exact ⟨u, m, hmono.trans (by rw [hu])⟩

/-- A Laurent polynomial over `ℤ` is a unit exactly when it is a monomial with an integer-unit coefficient. -/
theorem isUnit_iff {f : ℤ[T;T⁻¹]} :
    IsUnit f ↔ ∃ (u : ℤˣ) (n : ℤ), f = C (u : ℤ) * T n := by
  constructor
  · exact exists_eq_C_mul_T_of_isUnit
  · rintro ⟨u, n, rfl⟩
    exact (u.isUnit.map C).mul (isUnit_T n)

private theorem monomialUnit_coordinates (u : ℤˣ) (n : ℤ) :
    (if (monomialUnit u n).val.coeff
        (WithBot.unbotD 0 (monomialUnit u n).val.degree) = -1 then (-1 : ℤˣ) else 1,
      Multiplicative.ofAdd (WithBot.unbotD 0 (monomialUnit u n).val.degree)) =
        (u, Multiplicative.ofAdd n) := by
  rw [monomialUnit_coe, degree_C_mul_T n (u : ℤ) u.ne_zero]
  simp only [WithBot.unbotD_coe, ← single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
  congr 1
  apply Units.ext
  rcases Int.isUnit_eq_one_or u.isUnit with h | h <;> simp [h]

private theorem exists_monomialUnit (f : (ℤ[T;T⁻¹])ˣ) :
    ∃ (u : ℤˣ) (n : ℤ), f = monomialUnit u n := by
  obtain ⟨u, n, h⟩ := isUnit_iff.mp f.isUnit
  exact ⟨u, n, Units.ext (h.trans (monomialUnit_coe u n).symm)⟩

/-- The multiplicative unit group of `ℤ[T;T⁻¹]` is equivalent to `ℤˣ × Multiplicative ℤ`. -/
def intUnitsEquiv : (ℤ[T;T⁻¹])ˣ ≃* ℤˣ × Multiplicative ℤ where
  toFun f :=
    let n := WithBot.unbotD 0 f.val.degree
    (if f.val.coeff n = -1 then -1 else 1, Multiplicative.ofAdd n)
  invFun := unitsMulHom
  left_inv f := by
    obtain ⟨u, n, rfl⟩ := exists_monomialUnit f
    change unitsMulHom
      (if (monomialUnit u n).val.coeff
          (WithBot.unbotD 0 (monomialUnit u n).val.degree) = -1 then (-1 : ℤˣ) else 1,
        Multiplicative.ofAdd (WithBot.unbotD 0 (monomialUnit u n).val.degree)) =
          monomialUnit u n
    rw [monomialUnit_coordinates]
    rfl
  right_inv p := by
    rcases p with ⟨u, n⟩
    exact monomialUnit_coordinates u n.toAdd
  map_mul' f g := by
    obtain ⟨u, m, rfl⟩ := exists_monomialUnit f
    obtain ⟨v, n, rfl⟩ := exists_monomialUnit g
    have hmul : monomialUnit u m * monomialUnit v n = monomialUnit (u * v) (m + n) :=
      (unitsMulHom.map_mul (u, Multiplicative.ofAdd m) (v, Multiplicative.ofAdd n)).symm
    change (let f := monomialUnit u m * monomialUnit v n;
      (if f.val.coeff (WithBot.unbotD 0 f.val.degree) = -1 then (-1 : ℤˣ) else 1,
        Multiplicative.ofAdd (WithBot.unbotD 0 f.val.degree))) = _
    rw [hmul, monomialUnit_coordinates, monomialUnit_coordinates, monomialUnit_coordinates]
    rfl

/-- The classification equivalence sends the monomial unit `C u * T n` to `(u, n)`. -/
theorem intUnitsEquiv_apply (u : ℤˣ) (n : ℤ) :
    intUnitsEquiv (monomialUnit u n) = (u, Multiplicative.ofAdd n) :=
  monomialUnit_coordinates u n

/-- The inverse classification reconstructs the monomial unit `C u * T n.toAdd`. -/
theorem intUnitsEquiv_symm_apply (u : ℤˣ) (n : Multiplicative ℤ) :
    intUnitsEquiv.symm (u, n) = monomialUnit u n.toAdd :=
  rfl

/-- The additive group of units of `ℤ[T;T⁻¹]` is equivalent to `Additive ℤˣ × ℤ`. -/
def intUnitsAddEquiv : Additive (ℤ[T;T⁻¹])ˣ ≃+ Additive ℤˣ × ℤ :=
  (MulEquiv.toAdditive intUnitsEquiv).trans <|
    (AddEquiv.prodAdditive ℤˣ (Multiplicative ℤ)).trans
      (AddEquiv.prodCongr (AddEquiv.refl (Additive ℤˣ)) (AddEquiv.additiveMultiplicative ℤ))

/-- `intUnitsAddEquiv` is `intUnitsEquiv` after forgetting multiplication. -/
theorem intUnitsAddEquiv_apply (f : (ℤ[T;T⁻¹])ˣ) :
    intUnitsAddEquiv (Additive.ofMul f) =
      (Additive.ofMul (intUnitsEquiv f).fst, (intUnitsEquiv f).snd.toAdd) :=
  rfl

end LaurentPolynomial
