/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Additive valuations from homomorphisms on units

@stack 00IG

A nonarchimedean homomorphism from the unit group of a division ring determines an additive
valuation. The homomorphism and its nonarchimedean law are bundled so downstream API carries one
mathematical object rather than a map together with a repeated proof parameter.
-/

@[expose] public section

noncomputable section

universe u v

namespace AddValuation

variable {K : Type u} [DivisionRing K]
variable {Γ : Type v} [AddCommGroup Γ] [LinearOrder Γ]

/-- The nonarchimedean condition on an unbundled homomorphism from the unit group. -/
@[stacks 00IG "nonarchimedean homomorphism on units"]
structure IsNonarchimedeanOnUnits (v : Kˣ →* Multiplicative Γ) : Prop where
  map_add_ge_min :
    ∀ ⦃a b : K⦄, ∀ ha : a ≠ 0, ∀ hb : b ≠ 0, ∀ hab : a + b ≠ 0,
      min (Multiplicative.toAdd (v (Units.mk0 a ha)))
          (Multiplicative.toAdd (v (Units.mk0 b hb))) ≤
        Multiplicative.toAdd (v (Units.mk0 (a + b) hab))

/-- A homomorphism on the unit group equipped with its nonarchimedean law. -/
@[stacks 00IG "bundled nonarchimedean homomorphism on units"]
structure UnitHom (K : Type u) (Γ : Type v) [DivisionRing K] [AddCommGroup Γ] [LinearOrder Γ]
    extends Kˣ →* Multiplicative Γ where
  map_add_ge_min :
    ∀ ⦃a b : K⦄, ∀ ha : a ≠ 0, ∀ hb : b ≠ 0, ∀ hab : a + b ≠ 0,
      min (Multiplicative.toAdd (toMonoidHom (Units.mk0 a ha)))
          (Multiplicative.toAdd (toMonoidHom (Units.mk0 b hb))) ≤
        Multiplicative.toAdd (toMonoidHom (Units.mk0 (a + b) hab))

namespace UnitHom

instance instFunLike : FunLike (UnitHom K Γ) Kˣ (Multiplicative Γ) where
  coe u := u.toMonoidHom
  coe_injective u u' h := by
    cases u
    cases u'
    simp_all

instance instMonoidHomClass : MonoidHomClass (UnitHom K Γ) Kˣ (Multiplicative Γ) where
  map_mul u := u.toMonoidHom.map_mul
  map_one u := u.toMonoidHom.map_one

@[ext]
theorem ext {u u' : UnitHom K Γ} (h : ∀ x, u x = u' x) : u = u' := by
  apply DFunLike.coe_injective
  exact funext h

/-- Bundle an unbundled unit-group homomorphism and its nonarchimedean law. -/
@[stacks 00IG "bundle a nonarchimedean homomorphism on units"]
def of (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanOnUnits v) : UnitHom K Γ where
  toMonoidHom := v
  map_add_ge_min := hv.map_add_ge_min

@[simp, stacks 00IG "underlying homomorphism of a bundled unit homomorphism"]
theorem toMonoidHom_of (v : Kˣ →* Multiplicative Γ) (hv : IsNonarchimedeanOnUnits v) :
    (of v hv).toMonoidHom = v := rfl

/-- Recover the nonarchimedean law after forgetting a bundled unit homomorphism. -/
@[stacks 00IG "nonarchimedean law of a bundled unit homomorphism"]
theorem isNonarchimedeanOnUnits (u : UnitHom K Γ) :
    IsNonarchimedeanOnUnits u.toMonoidHom :=
  ⟨u.map_add_ge_min⟩

/-- Bundling the underlying homomorphism of a bundled unit homomorphism changes no data. -/
@[simp, stacks 00IG "bundle-forget round trip for unit homomorphisms"]
theorem of_toMonoidHom (u : UnitHom K Γ) :
    of u.toMonoidHom u.isNonarchimedeanOnUnits = u := by
  ext
  rfl

@[simp]
theorem coe_toMonoidHom (u : UnitHom K Γ) : u.toMonoidHom = u := rfl

/-- The exact additive value group of a bundled unit homomorphism. -/
@[stacks 00IG "exact value group of a homomorphism on units"]
abbrev ValueGroup (u : UnitHom K Γ) : AddSubgroup Γ := u.toMonoidHom.range.toAddSubgroup'

/-- Restrict a unit homomorphism to its exact additive value group. -/
@[stacks 00IG "restriction to the exact value group"]
def rangeRestrict (u : UnitHom K Γ) (x : Kˣ) : u.ValueGroup :=
  u.toMonoidHom.rangeRestrict x

@[simp, stacks 00IG "value of the restriction to the exact value group"]
theorem coe_rangeRestrict (u : UnitHom K Γ) (x : Kˣ) :
    (u.rangeRestrict x : Γ) = Multiplicative.toAdd (u x) := rfl

/-- Extend a unit homomorphism to the division ring, sending zero to `⊤`. -/
@[stacks 00IG "extended value of a homomorphism on units"]
noncomputable def value (u : UnitHom K Γ) (x : K) : WithTop u.ValueGroup := by
  classical
  exact if hx : x = 0 then ⊤ else (u.rangeRestrict (Units.mk0 x hx) : WithTop u.ValueGroup)

@[simp, stacks 00IG "unit-hom value at zero"]
theorem value_zero (u : UnitHom K Γ) : u.value 0 = ⊤ := by
  simp [value]

@[simp, stacks 00IG "unit-hom value at one"]
theorem value_one (u : UnitHom K Γ) : u.value 1 = 0 := by
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  unfold value
  split_ifs with h
  · exact (h1 h).elim
  · have hzero : u.rangeRestrict (Units.mk0 1 h) = 0 := by
      apply Subtype.ext
      change Multiplicative.toAdd (u (Units.mk0 1 h)) = 0
      simp [Units.mk0_one]
    simpa using hzero

variable [IsOrderedAddMonoid Γ]

omit [IsOrderedAddMonoid Γ] in
@[simp, stacks 00IG "unit-hom value on products"]
theorem value_mul (u : UnitHom K Γ) (a b : K) : u.value (a * b) = u.value a + u.value b := by
  by_cases ha : a = 0
  · simp [value, ha]
  by_cases hb : b = 0
  · simp [value, hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have hMul :
      u.value (a * b) =
        (u.rangeRestrict (Units.mk0 (a * b) hab) : WithTop u.ValueGroup) := by
    simp [value, hab]
  have hA : u.value a = (u.rangeRestrict (Units.mk0 a ha) : WithTop u.ValueGroup) := by
    simp [value, ha]
  have hB : u.value b = (u.rangeRestrict (Units.mk0 b hb) : WithTop u.ValueGroup) := by
    simp [value, hb]
  rw [hMul, hA, hB, ← WithTop.coe_add, WithTop.coe_eq_coe]
  apply Subtype.ext
  rw [Units.mk0_mul _ _ hab]
  change
    Multiplicative.toAdd (u (Units.mk0 a ha * Units.mk0 b hb)) =
      Multiplicative.toAdd (u (Units.mk0 a ha)) + Multiplicative.toAdd (u (Units.mk0 b hb))
  exact congrArg Multiplicative.toAdd
    (u.toMonoidHom.map_mul (Units.mk0 a ha) (Units.mk0 b hb))

omit [IsOrderedAddMonoid Γ] in
@[stacks 00IG "nonarchimedean inequality for the extended value"]
theorem min_value_le_value_add (u : UnitHom K Γ) (a b : K) :
    min (u.value a) (u.value b) ≤ u.value (a + b) := by
  by_cases hab : a + b = 0
  · rw [hab, value_zero]
    exact le_top
  by_cases ha : a = 0
  · subst a
    simp only [zero_add, value_zero, min_top_left, le_refl]
  by_cases hb : b = 0
  · subst b
    simp only [add_zero, value_zero, min_top_right, le_refl]
  have hA : u.value a = (u.rangeRestrict (Units.mk0 a ha) : WithTop u.ValueGroup) := by
    simp [value, ha]
  have hB : u.value b = (u.rangeRestrict (Units.mk0 b hb) : WithTop u.ValueGroup) := by
    simp [value, hb]
  have hAB :
      u.value (a + b) =
        (u.rangeRestrict (Units.mk0 (a + b) hab) : WithTop u.ValueGroup) := by
    simp [value, hab]
  rw [hA, hB, hAB, ← WithTop.coe_min, WithTop.coe_le_coe]
  change
    min (Multiplicative.toAdd (u.toMonoidHom (Units.mk0 a ha)))
        (Multiplicative.toAdd (u.toMonoidHom (Units.mk0 b hb))) ≤
      Multiplicative.toAdd (u.toMonoidHom (Units.mk0 (a + b) hab))
  exact u.map_add_ge_min (a := a) (b := b) ha hb hab

/-- The additive valuation induced by a bundled nonarchimedean homomorphism on units. -/
@[stacks 00IG "valuation induced by a homomorphism on units"]
def toAddValuation (u : UnitHom K Γ) : AddValuation K (WithTop u.ValueGroup) :=
  AddValuation.of u.value u.value_zero u.value_one u.min_value_le_value_add u.value_mul

/-- The induced valuation agrees with the original homomorphism away from zero. -/
@[simp, stacks 00IG "induced valuation away from zero"]
theorem toAddValuation_apply_of_ne (u : UnitHom K Γ) {x : K} (hx : x ≠ 0) :
    u.toAddValuation x = (u.rangeRestrict (Units.mk0 x hx) : WithTop u.ValueGroup) := by
  simp [toAddValuation, value, hx]

/-- The induced valuation agrees with the original homomorphism on units. -/
@[simp, stacks 00IG "induced valuation on units"]
theorem toAddValuation_apply_unit (u : UnitHom K Γ) (x : Kˣ) :
    u.toAddValuation x = (u.rangeRestrict x : WithTop u.ValueGroup) := by
  simp [toAddValuation, value, x.ne_zero]

/-- Every element of the exact value group is the value of a unit. -/
@[stacks 00IG "exact value group"]
theorem exists_unit_value_eq (u : UnitHom K Γ) (γ : u.ValueGroup) :
    ∃ x : Kˣ, u.toAddValuation x = (γ : WithTop u.ValueGroup) := by
  rcases u.toMonoidHom.rangeRestrict_surjective γ with ⟨x, rfl⟩
  exact ⟨x, u.toAddValuation_apply_unit x⟩

omit [IsOrderedAddMonoid Γ] in
@[simp, stacks 00IG "zero in the exact value group"]
theorem rangeRestrict_eq_zero_iff (u : UnitHom K Γ) (x : Kˣ) :
    ((u.rangeRestrict x : WithTop u.ValueGroup) = 0) ↔ Multiplicative.toAdd (u x) = 0 := by
  constructor
  · intro hx
    have hx' : u.rangeRestrict x = 0 := by simpa using hx
    exact congrArg Subtype.val hx'
  · intro hx
    have hx' : u.rangeRestrict x = 0 := by
      ext
      exact hx
    simpa using hx'

omit [IsOrderedAddMonoid Γ] in
@[stacks 00IG "nonnegative values in the exact value group"]
theorem rangeRestrict_nonneg_iff (u : UnitHom K Γ) (x : Kˣ) :
    0 ≤ (u.rangeRestrict x : WithTop u.ValueGroup) ↔ 0 ≤ Multiplicative.toAdd (u x) := by
  change
    (((0 : u.ValueGroup) : WithTop u.ValueGroup) ≤ (u.rangeRestrict x : WithTop u.ValueGroup)) ↔
      0 ≤ Multiplicative.toAdd (u x)
  rw [WithTop.coe_le_coe]
  rfl

omit [IsOrderedAddMonoid Γ] in
@[stacks 00IG "positive values in the exact value group"]
theorem rangeRestrict_pos_iff (u : UnitHom K Γ) (x : Kˣ) :
    0 < (u.rangeRestrict x : WithTop u.ValueGroup) ↔ 0 < Multiplicative.toAdd (u x) := by
  change
    (((0 : u.ValueGroup) : WithTop u.ValueGroup) < (u.rangeRestrict x : WithTop u.ValueGroup)) ↔
      0 < Multiplicative.toAdd (u x)
  rw [WithTop.coe_lt_coe]
  rfl

#synth MonoidHomClass (UnitHom K Γ) Kˣ (Multiplicative Γ)

end UnitHom

end AddValuation
