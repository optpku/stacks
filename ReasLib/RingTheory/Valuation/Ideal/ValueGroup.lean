/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Ideal
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Ideals of a Valuation Ring and Its Value Group

@stack 00IH

The ideal lattice of a valuation ring is identified with order ideals in the integral cone of its
canonical value group.
-/

universe u

namespace ValuationRing

/-- The integral cone `Γ_{≤ 1}` in the multiplicatively written canonical value group of a
valuation ring, including the zero value. -/
abbrev IntegralCone (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :=
  {gamma : ValueGroup A (FractionRing A) // gamma ≤ (1 : ValueGroup A (FractionRing A))}

/-- The canonical valuation of a ring element, regarded as a value in the integral cone. -/
noncomputable def integralValue
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a : A) : IntegralCone A :=
  ⟨valuation A (FractionRing A) (algebraMap A (FractionRing A) a),
    (mem_integer_iff A (FractionRing A) _).mpr ⟨a, rfl⟩⟩

/-- The value in the integral cone has the canonical valuation as its underlying value. -/
@[simp]
theorem integralValue_val
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a : A) :
    (integralValue A a).val = valuation A (FractionRing A) (algebraMap A (FractionRing A) a) :=
  rfl

/-- The order on integral values is reverse divisibility in the valuation ring. -/
theorem integralValue_le_iff_dvd
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a b : A) :
    integralValue A a ≤ integralValue A b ↔ b ∣ a := by
  change (∃ c : A, c • algebraMap A (FractionRing A) b =
    algebraMap A (FractionRing A) a) ↔ b ∣ a
  simp only [Algebra.smul_def, ← map_mul,
    (IsFractionRing.injective A (FractionRing A)).eq_iff, dvd_def, mul_comm, eq_comm]

/-- Every element of the integral cone is the value of a ring element. -/
theorem integralValue_surjective
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    Function.Surjective (integralValue A) := by
  rintro ⟨⟨x⟩, hx⟩
  obtain ⟨a, ha⟩ := (mem_integer_iff A (FractionRing A) x).mp hx
  exact ⟨a, Subtype.ext (congrArg (valuation A (FractionRing A)) ha)⟩

/-- The value of one is the largest element of the integral cone. -/
@[simp]
theorem integralValue_one
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    integralValue A 1 = ⟨1, le_rfl⟩ := by
  apply Subtype.ext
  simp [integralValue]

/-- Integral values respect multiplication. -/
theorem integralValue_mul
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (a b : A) :
    integralValue A (a * b) =
      ⟨(integralValue A a).val * (integralValue A b).val,
        mul_le_one' (integralValue A a).property (integralValue A b).property⟩ := by
  apply Subtype.ext
  simp [integralValue]

end ValuationRing

namespace Order.Ideal

/-- The multiplicative form of primality for an order ideal in the integral cone of a valuation
ring's canonical value group. -/
def IsValuationPrime
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (J : Order.Ideal (ValuationRing.IntegralCone A)) : Prop :=
  (⟨1, le_rfl⟩ : ValuationRing.IntegralCone A) ∉ J ∧
    ∀ ⦃gamma delta : ValuationRing.ValueGroup A (FractionRing A)⦄,
      ∀ hgamma : gamma ≤ 1, ∀ hdelta : delta ≤ 1,
        (⟨gamma * delta, mul_le_one' hgamma hdelta⟩ : ValuationRing.IntegralCone A) ∈ J →
          (⟨gamma, hgamma⟩ : ValuationRing.IntegralCone A) ∈ J ∨
            (⟨delta, hdelta⟩ : ValuationRing.IntegralCone A) ∈ J

end Order.Ideal

namespace ValuationRing

/-- Lemma 10.50.17 (1): ideals of a valuation ring correspond order-isomorphically to order ideals
in the integral cone of its canonical value group. -/
@[stacks 00IH "(1) ideal correspondence"]
noncomputable def idealOrderIso
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    Ideal A ≃o Order.Ideal (IntegralCone A) where
  toFun I :=
    { carrier := integralValue A '' (I : Set A)
      lower' := by
        rintro delta gamma hle ⟨b, hb, rfl⟩
        obtain ⟨a, rfl⟩ := integralValue_surjective A gamma
        exact ⟨a, I.mem_of_dvd ((integralValue_le_iff_dvd A a b).mp hle) hb, rfl⟩
      nonempty' := ⟨integralValue A 0, 0, I.zero_mem, rfl⟩
      directed' := by
        intro gamma hgamma delta hdelta
        rcases le_total gamma delta with h | h
        · exact ⟨delta, hdelta, h, le_rfl⟩
        · exact ⟨gamma, hgamma, le_rfl, h⟩ }
  invFun J :=
    { carrier := {a : A | integralValue A a ∈ J}
      zero_mem' := by
        obtain ⟨gamma, hgamma⟩ := J.nonempty
        apply J.lower (show integralValue A 0 ≤ gamma from ?_) hgamma
        change valuation A (FractionRing A) (algebraMap A (FractionRing A) 0) ≤ gamma.val
        simp
      add_mem' := by
        intro a b ha hb
        have hsum : integralValue A (a + b) ≤ max (integralValue A a) (integralValue A b) := by
          change valuation A (FractionRing A) (algebraMap A (FractionRing A) (a + b)) ≤
            max (valuation A (FractionRing A) (algebraMap A (FractionRing A) a))
              (valuation A (FractionRing A) (algebraMap A (FractionRing A) b))
          rw [map_add]
          exact (valuation A (FractionRing A)).map_add _ _
        rcases le_total (integralValue A a) (integralValue A b) with h | h
        · exact J.lower (hsum.trans (max_le h le_rfl)) hb
        · exact J.lower (hsum.trans (max_le le_rfl h)) ha
      smul_mem' := by
        intro a b hb
        apply J.lower ?_ hb
        exact (integralValue_le_iff_dvd A (a • b) b).mpr
          ⟨a, by simp [smul_eq_mul, mul_comm]⟩ }
  left_inv := by
    intro I
    apply Ideal.ext
    intro a
    change (∃ b ∈ I, integralValue A b = integralValue A a) ↔ a ∈ I
    constructor
    · rintro ⟨b, hb, hba⟩
      exact I.mem_of_dvd ((integralValue_le_iff_dvd A a b).mp (le_of_eq hba.symm)) hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  right_inv := by
    intro J
    apply SetLike.ext
    intro gamma
    change (∃ a, integralValue A a ∈ J ∧ integralValue A a = gamma) ↔ gamma ∈ J
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hgamma
      obtain ⟨a, rfl⟩ := integralValue_surjective A gamma
      exact ⟨a, hgamma, rfl⟩
  map_rel_iff' := by
    intro I K
    change (integralValue A '' (I : Set A) ⊆ integralValue A '' (K : Set A)) ↔ I ≤ K
    constructor
    · intro h a ha
      obtain ⟨b, hb, hba⟩ := h ⟨a, ha, rfl⟩
      exact K.mem_of_dvd ((integralValue_le_iff_dvd A a b).mp (le_of_eq hba.symm)) hb
    · rintro h _ ⟨a, ha, rfl⟩
      exact ⟨a, h ha, rfl⟩

/-- An integral value lies in the corresponding order ideal precisely when it is the value
of an element of the ring ideal. -/
@[simp, stacks 00IH "(1) values of an ideal"]
theorem mem_idealOrderIso
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (I : Ideal A) (gamma : IntegralCone A) :
    gamma ∈ idealOrderIso A I ↔ ∃ a ∈ I, integralValue A a = gamma := by
  rfl

/-- The inverse correspondence consists of the ring elements whose values lie in the order
ideal. -/
@[simp, stacks 00IH "(1) ideal of an order ideal"]
theorem mem_idealOrderIso_symm
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (J : Order.Ideal (IntegralCone A)) (a : A) :
    a ∈ (idealOrderIso A).symm J ↔ integralValue A a ∈ J := by
  rfl

/-- Membership in a ring ideal depends only on the integral value. -/
@[simp]
theorem integralValue_mem_idealOrderIso
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    (I : Ideal A) (a : A) :
    integralValue A a ∈ idealOrderIso A I ↔ a ∈ I := by
  rw [mem_idealOrderIso]
  constructor
  · rintro ⟨b, hb, hba⟩
    exact I.mem_of_dvd ((integralValue_le_iff_dvd A a b).mp (le_of_eq hba.symm)) hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- The zero ring ideal corresponds to the singleton zero-value order ideal. -/
@[simp, stacks 00IH "(1) zero ideal"]
theorem idealOrderIso_bot
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] :
    idealOrderIso A ⊥ = Order.Ideal.principal (integralValue A 0) := by
  apply SetLike.ext
  intro gamma
  rw [mem_idealOrderIso, Order.Ideal.mem_principal]
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha0 : a = 0 := by simpa using ha
    subst a
    exact le_rfl
  · intro hgamma
    obtain ⟨a, rfl⟩ := integralValue_surjective A gamma
    have ha : a = 0 := by
      simpa using (integralValue_le_iff_dvd A a 0).mp hgamma
    exact ⟨a, by simp [ha], rfl⟩

/-- Lemma 10.50.17 (2): `idealOrderIso` identifies prime ideals with multiplicatively prime order
ideals. -/
@[stacks 00IH "(2) prime ideals"]
theorem idealOrderIso_isPrime_iff
    (A : Type u) [CommRing A] [IsDomain A] [ValuationRing A] (I : Ideal A) :
    I.IsPrime ↔ Order.Ideal.IsValuationPrime A (idealOrderIso A I) := by
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · simpa only [← integralValue_one A, integralValue_mem_idealOrderIso] using hI.one_notMem
    · intro gamma delta hgamma hdelta hprod
      obtain ⟨a, ha⟩ := integralValue_surjective A ⟨gamma, hgamma⟩
      obtain ⟨b, hb⟩ := integralValue_surjective A ⟨delta, hdelta⟩
      have hab : integralValue A (a * b) =
          ⟨gamma * delta, mul_le_one' hgamma hdelta⟩ := by
        simpa only [ha, hb] using integralValue_mul A a b
      have hm : a * b ∈ I := (integralValue_mem_idealOrderIso A I _).mp (hab.symm ▸ hprod)
      simpa only [ha, hb] using
        (hI.mem_or_mem hm).imp
          (fun h => (integralValue_mem_idealOrderIso A I a).mpr h)
          (fun h => (integralValue_mem_idealOrderIso A I b).mpr h)
  · rintro ⟨hone, hmul⟩
    refine ⟨?_, ?_⟩
    · intro htop
      apply hone
      rw [← integralValue_one A, integralValue_mem_idealOrderIso, htop]
      trivial
    · intro a b hab
      have habv := (integralValue_mem_idealOrderIso A I (a * b)).mpr hab
      rw [integralValue_mul] at habv
      have h := hmul (integralValue A a).property (integralValue A b).property habv
      simpa only [Subtype.coe_eta, integralValue_mem_idealOrderIso] using h

end ValuationRing
