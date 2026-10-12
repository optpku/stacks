/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.RingTheory.AdicCompletion.Quotient
public import ReasLib.RingTheory.DividedPowers.Category
public import ReasLib.RingTheory.DividedPowers.Quotient
public import ReasLib.RingTheory.Localization.AtPrime.Int

@[expose] public section

/-!
# Adic completion of divided power rings

This file separates three reusable layers of the completion construction:

* divided powers respect congruence modulo powers of a principal ideal;
* stable ideal-power quotients form a canonical sequential inverse system;
* the completed divided power ring carries a canonical cone over that system.

The final results specialize these constructions to the `p`-adic setting.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace DividedPowers

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- Divided powers preserve congruence modulo every power of a
principal ideal acting on the divided power ideal.  This is the algebraic continuity statement
used by completion. -/
@[stacks 07KD "(3), principal-adic continuity"]
theorem dpow_sub_mem_principalPow_mul (γ : DividedPowers I) (r : A) (n e : ℕ)
    {x y : A} (hx : x ∈ I) (hy : y ∈ I)
    (hxy : x - y ∈ Ideal.span {r} ^ e * I) :
    γ.dpow n x - γ.dpow n y ∈ Ideal.span {r} ^ e * I := sorry

/-- Divided powers are stable under powers of `J` from stage `offset` onward when every
intersection `J ^ (e + offset) ⊓ I` is a sub-divided-power ideal. -/
@[stacks 07KD "eventual stability under ideal powers"]
def IsStableUnderPowers (γ : DividedPowers I) (J : Ideal A) (offset : ℕ) : Prop :=
  ∀ e : ℕ, IsSubDPIdeal γ (J ^ (e + offset) ⊓ I)

/-- The defining expansion of `IsStableUnderPowers`. -/
theorem isStableUnderPowers_iff (γ : DividedPowers I) (J : Ideal A) (offset : ℕ) :
    γ.IsStableUnderPowers J offset ↔
      ∀ e : ℕ, IsSubDPIdeal γ (J ^ (e + offset) ⊓ I) := sorry

/-- If the `n`th power of a principal ideal lies in the divided-power ideal, its powers
are stable under divided powers from exponent `2 * n` onward. -/
theorem isStableUnderPowers_principal (γ : DividedPowers I) (r : A) (n : ℕ)
    (h : Ideal.span {r} ^ n ≤ I) :
    γ.IsStableUnderPowers (Ideal.span {r}) (2 * n) := sorry

namespace QuotientPowerTower

variable (γ : DividedPowers I) (J : Ideal A) (offset : ℕ)
variable (hstable : γ.IsStableUnderPowers J offset)

/-- The `e`th divided power quotient after the chosen stable offset. -/
noncomputable abbrev stage (e : ℕ) : DividedPowerRing :=
  DividedPowerRing.of (A ⧸ J ^ (e + offset))
    (I.map (Ideal.Quotient.mk (J ^ (e + offset))))
    (DividedPowers.Quotient.dividedPowers γ (hstable e))

/-- The containment of consecutive powers defining the quotient transition map. -/
theorem pow_succ_add_le (e : ℕ) :
    J ^ ((e + 1) + offset) ≤ J ^ (e + offset) := sorry

/-- The factor map between consecutive stable quotients preserves their induced divided
power structures. -/
theorem factor_isDPMorphism (e : ℕ) :
    IsDPMorphism
      (DividedPowers.Quotient.dividedPowers γ (hstable (e + 1)))
      (DividedPowers.Quotient.dividedPowers γ (hstable e))
      (Ideal.Quotient.factor (pow_succ_add_le J offset e)) := sorry

/-- The canonical transition from stage `e + 1` to stage `e`. -/
noncomputable def step (e : ℕ) :
    stage γ J offset hstable (e + 1) ⟶ stage γ J offset hstable e :=
  DPMorphism.mk' (factor_isDPMorphism γ J offset hstable e)

/-- The canonical inverse system of stable ideal-power quotients in divided power rings. -/
@[stacks 07KD "canonical divided power quotient tower"]
noncomputable def diagram : ℕᵒᵖ ⥤ DividedPowerRing :=
  Functor.ofOpSequence (step γ J offset hstable)

/-- The successor map of the quotient-power diagram is its canonical factor map. -/
theorem diagram_step (e : ℕ) :
    (diagram γ J offset hstable).map
        (CategoryTheory.homOfLE (Nat.le_add_right e 1)).op =
      step γ J offset hstable e := sorry

variable (hpow : J ^ offset ≤ I)
variable (γhat : DividedPowers (RingHom.ker (AdicCompletion.toQuotient J I offset hpow)))

/-- The completed divided power ring at the cone point. -/
noncomputable abbrev completion : DividedPowerRing :=
  DividedPowerRing.of (AdicCompletion J A)
    (RingHom.ker (AdicCompletion.toQuotient J I offset hpow)) γhat

/-- Evaluation at every stable quotient stage preserves any
compatible divided powers on the completion. -/
@[stacks 07KD "(3), compatibility with quotient-stage evaluation"]
theorem eval_isDPMorphism
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) (e : ℕ) :
    IsDPMorphism γhat
      (DividedPowers.Quotient.dividedPowers γ (hstable e))
      (AdicCompletion.evalₐ J (e + offset)).toRingHom := sorry

/-- The canonical morphism from the completed divided power ring to the `e`th quotient stage. -/
noncomputable def leg
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) (e : ℕ) :
    completion J offset hpow γhat ⟶ stage γ J offset hstable e :=
  DPMorphism.mk' (eval_isDPMorphism γ J offset hstable hpow γhat hγhat e)

/-- The completion legs commute with the successor transitions of the quotient tower. -/
theorem leg_naturality
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) (e : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (completion J offset hpow γhat)).map
          (CategoryTheory.homOfLE (Nat.le_add_right e 1)).op ≫
        leg γ J offset hstable hpow γhat hγhat e =
      leg γ J offset hstable hpow γhat hγhat (e + 1) ≫
        (diagram γ J offset hstable).map
          (CategoryTheory.homOfLE (Nat.le_add_right e 1)).op := sorry

/-- The canonical cone from the completed divided power ring to its stable quotient-power
diagram. -/
@[stacks 07KD "canonical cone from a completed divided power ring"]
noncomputable def cone
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) :
    Cone (diagram γ J offset hstable) where
  pt := completion J offset hpow γhat
  π := NatTrans.ofOpSequence
    (fun e ↦ leg γ J offset hstable hpow γhat hγhat e)
    (leg_naturality γ J offset hstable hpow γhat hγhat)

/-- The `e`th component of the completion cone is adic evaluation at `e + offset`. -/
theorem cone_π_app
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) (e : ℕ) :
    (cone γ J offset hstable hpow γhat hγhat).π.app (op e) =
      leg γ J offset hstable hpow γhat hγhat e := sorry

/-- The compatible family of quotient maps underlying the lift from an arbitrary cone.  At
index `n` it uses the cone map to the `(n + offset)`th quotient and then forgets down to the
`n`th quotient. -/
noncomputable def liftFamily (s : Cone (diagram γ J offset hstable)) (n : ℕ) :
    s.pt →+* A ⧸ J ^ n :=
  (Ideal.Quotient.factorPow J (Nat.le_add_right n offset)).comp
    (s.π.app (op n)).toRingHom

/-- The quotient maps extracted from a cone form an adically compatible family. -/
theorem liftFamily_compat (s : Cone (diagram γ J offset hstable)) {m n : ℕ}
    (h : m ≤ n) :
    (Ideal.Quotient.factorPow J h).comp (liftFamily γ J offset hstable s n) =
      liftFamily γ J offset hstable s m := sorry

/-- The explicit underlying ring map from an arbitrary cone vertex to the adic completion. -/
noncomputable def liftRingHom (s : Cone (diagram γ J offset hstable)) :
    s.pt →+* AdicCompletion J A :=
  AdicCompletion.liftRingHom J (liftFamily γ J offset hstable s)
    (liftFamily_compat γ J offset hstable s)

/-- The explicit adic lift preserves the supplied divided powers on the completion. -/
theorem liftRingHom_isDPMorphism
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A)))
    (s : Cone (diagram γ J offset hstable)) :
    IsDPMorphism s.pt.dividedPowers γhat
      (liftRingHom γ J offset hstable s) := sorry

/-- The canonical divided-power morphism from an arbitrary cone vertex to the completed cone
point. -/
noncomputable def lift
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A)))
    (s : Cone (diagram γ J offset hstable)) :
    s.pt ⟶ completion J offset hpow γhat :=
  DPMorphism.mk'
    (liftRingHom_isDPMorphism γ J offset hstable hpow γhat hγhat s)

/-- The underlying ring map of the canonical divided-power lift is the adic lift. -/
theorem lift_toRingHom
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A)))
    (s : Cone (diagram γ J offset hstable)) :
    (lift γ J offset hstable hpow γhat hγhat s).toRingHom =
      liftRingHom γ J offset hstable s := sorry

/-- The completed divided-power ring is the limit of its
stable quotient-power tower.  The limiting lift is the explicit adic lift above. -/
@[stacks 07KD "moreover, adic completion as a divided-power limit"]
noncomputable def isLimit
    (hγhat : IsDPMorphism γ γhat (algebraMap A (AdicCompletion J A))) :
    IsLimit (cone γ J offset hstable hpow γhat hγhat) where
  lift s := lift γ J offset hstable hpow γhat hγhat s
  fac := sorry
  uniq := sorry

end QuotientPowerTower

/-- A divided power structure admits a compatible extension to the completed ideal in a
principal-adic completion. -/
theorem exists_principalCompletionExtension (γ : DividedPowers I) (r : A) (n : ℕ)
    (h : Ideal.span {r} ^ n ≤ I) :
    ∃ γhat : DividedPowers
        (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {r}) I n h)),
      IsDPMorphism γ γhat (algebraMap A (AdicCompletion (Ideal.span {r}) A)) := sorry

/-- Two divided power structures on the completed ideal which extend the same divided powers
along the completion map are equal. -/
theorem principalCompletionExtension_unique (γ : DividedPowers I) (r : A) (n : ℕ)
    (h : Ideal.span {r} ^ n ≤ I)
    {γhat δhat : DividedPowers
      (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {r}) I n h))}
    (hγhat : IsDPMorphism γ γhat
      (algebraMap A (AdicCompletion (Ideal.span {r}) A)))
    (hδhat : IsDPMorphism γ δhat
      (algebraMap A (AdicCompletion (Ideal.span {r}) A))) :
    γhat = δhat := sorry

/-- Divided powers extend uniquely from `I` to the completed
ideal in a principal-adic completion. -/
@[stacks 07KD "(3), unique extension to a principal-adic completion"]
theorem existsUnique_principalCompletionExtension (γ : DividedPowers I) (r : A) (n : ℕ)
    (h : Ideal.span {r} ^ n ≤ I) :
    ∃! γhat : DividedPowers
        (RingHom.ker (AdicCompletion.toQuotient (Ideal.span {r}) I n h)),
      IsDPMorphism γ γhat (algebraMap A (AdicCompletion (Ideal.span {r}) A)) := sorry

/-- Over a `ℤ_(p)`-algebra, sufficiently high powers of `p`
are contained in `I` and are stable under its divided powers. -/
@[stacks 07KD "moreover, eventual stability of p-power ideals"]
theorem eventually_stable_primePowers (γ : DividedPowers I) (p : ℕ) [Fact p.Prime]
    [Algebra (Int.LocalizationAtPrime p) A] (n : ℕ)
    (h : Ideal.span {(p : A)} ^ n ≤ I) :
    ∃ offset : ℕ,
      Ideal.span {(p : A)} ^ offset ≤ I ∧
        γ.IsStableUnderPowers (Ideal.span {(p : A)}) offset := sorry

end DividedPowers
