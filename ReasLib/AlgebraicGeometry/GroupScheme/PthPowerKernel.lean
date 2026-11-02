/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReasLib.AlgebraicGeometry.AffineSpace.AdditiveGroup
public import ReasLib.AlgebraicGeometry.GroupScheme.Subgroup.Factorization
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.MvPolynomial.PthPowerKernel

/-!
# Homogeneous p-th-power kernel group schemes

This module constructs the closed additive subgroup scheme defined by the homogeneous relation
`X₀ ^ p + α * X₁ ^ p` and records its geometric properties over a field of characteristic `p`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry MonoidalCategory CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.PthPowerKernel

open AffineSpace
open MvPolynomial.PthPowerKernel

/-- The homogeneous p-th-power kernel viewed as a scheme over `Spec k`. -/
def over {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    Over (Spec (CommRingCat.of.{u} k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α))))

/-- The underlying affine scheme `V(X₀ ^ p + α * X₁ ^ p)`. -/
abbrev scheme {k : Type u} [CommRing k] (p : ℕ) (α : k) : Scheme :=
  (over p α).left

/-- The structure morphism of `scheme p α` to `Spec k`. -/
abbrev toBase {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    scheme p α ⟶ Spec (CommRingCat.of.{u} k) :=
  (over p α).hom

/-- The affine plane over `Spec k` equipped with coordinatewise addition. -/
abbrev ambient {k : Type u} [CommRing k] : Over (Spec (CommRingCat.of.{u} k)) :=
  Scheme.asOver (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of.{u} k)))
    (Spec (CommRingCat.of.{u} k))

/-- The quotient-presentation morphism into `Spec k[X₀, X₁]`. -/
def inclusionToSpec {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    scheme p α ⟶ Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span ({relation p α} :
      Set (MvPolynomial (ULift.{u} (Fin 2)) k))))
  )

/-- The closed embedding of the homogeneous p-th-power kernel into the affine plane. -/
def inclusion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    over p α ⟶ ambient :=
  Over.homMk
    (inclusionToSpec p α ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv)
    (by
      change inclusionToSpec p α ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv ≫
          𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of.{u} k)) ↘ Spec (CommRingCat.of.{u} k) = _
      rw [AffineSpace.SpecIso_inv_over]
      change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
        Spec.map (CommRingCat.ofHom MvPolynomial.C) =
          Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α)))
      rw [← Spec.map_comp]
      rfl)

/-- The quotient presentation is a closed immersion into `Spec k[X₀, X₁]`. -/
instance inclusionToSpec_isClosedImmersion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    IsClosedImmersion (inclusionToSpec p α) := by
  let I : Ideal (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
    Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
  change IsClosedImmersion
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
        Spec (CommRingCat.of ((MvPolynomial (ULift.{u} (Fin 2)) k) ⧸ I)) ⟶
          Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)))
  simpa [I] using
    (IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective)

/-- The homogeneous p-th-power kernel is a closed subscheme of the affine plane. -/
instance inclusion_isClosedImmersion {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    IsClosedImmersion (inclusion p α).left := by
  change IsClosedImmersion
      (inclusionToSpec p α ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).inv)
  infer_instance

/-- The inclusion pulls an affine coordinate back to its quotient class. -/
theorem inclusion_appTop_coord {k : Type u} [CommRing k] (p : ℕ) (α : k) (i : ULift.{u} (Fin 2)) :
    (inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) i) =
      (Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv
        (Ideal.Quotient.mk (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k)))
          (MvPolynomial.X i)) := by
  let I := Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
  let q : CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k) ⟶ CommRingCat.of (Ring p α) :=
    CommRingCat.ofHom (Ideal.Quotient.mk I)
  calc
    (inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) i) =
        (Spec.map q).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv
            (MvPolynomial.X i)) :=
      congrArg (fun r => (Spec.map q).appTop r)
        (AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of k) i)
    _ = _ := by
      exact congrArg (fun h : CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k) ⟶
          Γ(Spec (CommRingCat.of (Ring p α)), ⊤) => h (MvPolynomial.X i))
        (Scheme.ΓSpecIso_inv_naturality q).symm

/-- Pullback of a scalar along the structure morphism is the quotient algebra map. -/
theorem toBase_appTop {k : Type u} [CommRing k] (p : ℕ) (α r : k) :
    (toBase p α).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) =
      (Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv (algebraMap k (Ring p α) r) := by
  change ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α)))).appTop) r = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- The defining equation vanishes on the quotient-presentation inclusion. -/
theorem inclusion_relation {k : Type u} [CommRing k] (p : ℕ) (α : k) :
    (inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) (ULift.up (0 : Fin 2))) ^ p +
      (toBase p α).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv α) *
        (inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) (ULift.up (1 : Fin 2))) ^ p = 0 := by
  rw [inclusion_appTop_coord, inclusion_appTop_coord, toBase_appTop]
  let I := Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
  have hrel' : Ideal.Quotient.mk I
      (MvPolynomial.X (ULift.up (0 : Fin 2)) ^ p +
        MvPolynomial.C α * MvPolynomial.X (ULift.up (1 : Fin 2)) ^ p) =
      (0 : Ring p α) := quotient_relation_eq_zero p α
  have hC : Ideal.Quotient.mk I (MvPolynomial.C α) = algebraMap k (Ring p α) α := rfl
  have hrel : Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))) ^ p +
      algebraMap k (Ring p α) α *
        Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))) ^ p =
      (0 : Ring p α) := by
    simpa only [map_add, map_mul, map_pow, hC] using hrel'
  have h := congrArg (fun r : Ring p α =>
    (Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv r) hrel
  simp only [map_add, map_mul, map_pow, map_zero] at h
  exact h

section GroupStructure

variable (p : ℕ) {k : Type u} [CommRing k] (α : k)

/-- The unit of the additive group scheme factored through the p-th-power kernel. -/
def oneLeft [Fact p.Prime] :
    (𝟙_ (Over (Spec (CommRingCat.of.{u} k)))).left ⟶ scheme p α :=
  let I : Ideal (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
    Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
  let φ : MvPolynomial (ULift.{u} (Fin 2)) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ ↦ 0)
  let φbar : Ring p α →+* k :=
    Ideal.Quotient.lift I φ <| by
      intro r hr
      rcases Ideal.mem_span_singleton.mp hr with ⟨s, rfl⟩
      have hφ : φ (relation p α) = 0 := by
        change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ (0 : k)) (relation p α) = 0
        rw [eval_relation]
        have hp : p ≠ 0 := Nat.Prime.ne_zero (Fact.out : Nat.Prime p)
        simp [zero_pow hp]
      rw [map_mul, hφ, zero_mul]
  Spec.map (CommRingCat.ofHom φbar)

/-- Ambient addition sends the defining ideal into the kernel of its pullback on sections. -/
theorem addition_relation [Fact p.Prime] [CharP k p] :
    Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k)) ≤
      RingHom.ker (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv ≫
        (((inclusion p α ⊗ₘ inclusion p α) ≫ μ[ambient]).left ≫
          (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k)).hom).appTop).hom) := by
  let H := over p α
  let G : Over (Spec (CommRingCat.of k)) := ambient
  let F : H ⊗ H ⟶ G := (inclusion p α ⊗ₘ inclusion p α) ≫ μ[G]
  let z := (Scheme.ΓSpecIso (CommRingCat.of k)).inv α
  let b : k →+* Γ((H ⊗ H).left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (H ⊗ H).hom.appTop).hom
  let x (g : H ⊗ H ⟶ H) (i : ULift.{u} (Fin 2)) :=
    (g ≫ inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) i)
  have coeff (g : H ⊗ H ⟶ H) :
      g.left.appTop ((toBase p α).appTop z) = b α := by
    exact congrArg (fun t : (H ⊗ H).left ⟶ Spec (CommRingCat.of k) => t.appTop z) (Over.w g)
  have rel (g : H ⊗ H ⟶ H) :
      x g (ULift.up (0 : Fin 2)) ^ p +
        b α * x g (ULift.up (1 : Fin 2)) ^ p = 0 := by
    have hc : g.left.appTop ((toBase p α).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv α)) = b α := coeff g
    have h := congrArg (fun r => g.left.appTop r) (inclusion_relation p α)
    simp only [map_add, map_mul, map_pow, map_zero, hc] at h
    exact h
  have coeffF : F.left.appTop
      ((𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop z) =
      b α := by
    exact congrArg (fun t : (H ⊗ H).left ⟶ Spec (CommRingCat.of k) => t.appTop z) (Over.w F)
  have hadd (i : ULift.{u} (Fin 2)) :
      F.left.appTop (coord (Spec (CommRingCat.of k)) i) =
        x (CartesianMonoidalCategory.fst H H) i + x (CartesianMonoidalCategory.snd H H) i := by
    have ha : μ[G].left.appTop (coord (Spec (CommRingCat.of k)) i) =
        (CartesianMonoidalCategory.fst G G).left.appTop (coord (Spec (CommRingCat.of k)) i) +
          (CartesianMonoidalCategory.snd G G).left.appTop (coord (Spec (CommRingCat.of k)) i) :=
      AffineSpace.homOfVector_appTop_coord _ _ _
    have hf := congrArg
      (fun g : H ⊗ H ⟶ G => g.left.appTop (coord (Spec (CommRingCat.of k)) i))
      (CartesianMonoidalCategory.tensorHom_fst (inclusion p α) (inclusion p α))
    have hs := congrArg
      (fun g : H ⊗ H ⟶ G => g.left.appTop (coord (Spec (CommRingCat.of k)) i))
      (CartesianMonoidalCategory.tensorHom_snd (inclusion p α) (inclusion p α))
    calc
      F.left.appTop (coord (Spec (CommRingCat.of k)) i) =
          (inclusion p α ⊗ₘ inclusion p α).left.appTop
            (μ[G].left.appTop (coord (Spec (CommRingCat.of k)) i)) := rfl
      _ = _ := congrArg (fun r => (inclusion p α ⊗ₘ inclusion p α).left.appTop r) ha
      _ = _ := map_add (inclusion p α ⊗ₘ inclusion p α).left.appTop.hom _ _
      _ = _ := congrArg₂ (· + ·) hf hs
  have hpzero : (p : Γ((H ⊗ H).left, ⊤)) = 0 := by
    rw [← map_natCast b p, CharP.cast_eq_zero k p, map_zero]
  have hpow (a c : Γ((H ⊗ H).left, ⊤)) : (a + c) ^ p = a ^ p + c ^ p := by
    simpa only [hpzero, zero_mul, _root_.add_zero] using add_pow_prime_eq (Fact.out : p.Prime) a c
  have he : ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv ≫
      (F.left ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k)).hom).appTop) =
      CommRingCat.ofHom (MvPolynomial.eval₂Hom
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop).hom)
          (coord (Spec (CommRingCat.of k)))) ≫ F.left.appTop := by
    rw [Scheme.Hom.comp_appTop, AffineSpace.SpecIso_hom_appTop]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change F.left.appTop (MvPolynomial.eval₂
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop).hom)
      (coord (Spec (CommRingCat.of k)))
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv r))) =
      F.left.appTop (MvPolynomial.eval₂
        (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop).hom)
        (coord (Spec (CommRingCat.of k))) r)
    have hr := congrArg (fun h : CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k) ⟶
        CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k) => h r)
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv_hom_id
    change (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv r) = r at hr
    rw [hr]
  apply Ideal.span_le.mpr
  rintro r (rfl : r = relation p α)
  change (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))).inv ≫
    (F.left ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k)).hom).appTop).hom)
      (relation p α) = 0
  rw [he]
  change F.left.appTop (MvPolynomial.eval₂
    (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop).hom)
      (coord (Spec (CommRingCat.of k))) (relation p α)) = 0
  rw [eval_relation]
  change F.left.appTop
    ((coord (Spec (CommRingCat.of k)) (ULift.up (0 : Fin 2)) :
        Γ(𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), ⊤)) ^ p +
      (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)).appTop z *
        (coord (Spec (CommRingCat.of k)) (ULift.up (1 : Fin 2)) :
          Γ(𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)), ⊤)) ^ p) = 0
  erw [map_add, map_mul, map_pow, map_pow, coeffF, hadd, hadd, hpow, hpow]
  calc
    _ = (x (CartesianMonoidalCategory.fst H H) (ULift.up (0 : Fin 2)) ^ p +
        b α * x (CartesianMonoidalCategory.fst H H) (ULift.up (1 : Fin 2)) ^ p) +
      (x (CartesianMonoidalCategory.snd H H) (ULift.up (0 : Fin 2)) ^ p +
        b α * x (CartesianMonoidalCategory.snd H H) (ULift.up (1 : Fin 2)) ^ p) := by ring
    _ = 0 := by rw [rel, rel, _root_.add_zero]

/-- Coordinatewise addition on the affine plane factored through the p-th-power kernel. -/
def mulLeft [Fact p.Prime] [CharP k p] :
    (over p α ⊗ over p α).left ⟶ scheme p α :=
  let G : Over (Spec (CommRingCat.of.{u} k)) := ambient
  let f : (over p α ⊗ over p α).left ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
    ((inclusion p α ⊗ₘ inclusion p α) ≫ μ[G]).left ≫
      (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of.{u} k)).hom
  Scheme.Hom.liftQuotient f
    (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k)))
    (addition_relation p α)

/-- Coordinatewise inversion on the affine plane factored through the p-th-power kernel. -/
def invLeft :
    (over p α).left ⟶ scheme p α :=
  let I : Ideal (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)) :=
    Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
  let ψ : MvPolynomial (ULift.{u} (Fin 2)) k →+* Ring p α :=
    MvPolynomial.eval₂Hom (algebraMap k (Ring p α))
      (fun i ↦ -Ideal.Quotient.mk I (MvPolynomial.X i))
  let ψbar : Ring p α →+* Ring p α :=
    Ideal.Quotient.lift I ψ <| by
      intro r hr
      rcases Ideal.mem_span_singleton.mp hr with ⟨s, rfl⟩
      have hψ :
          ψ (relation p α) = 0 := by
        change MvPolynomial.eval₂ (algebraMap k (Ring p α))
            (fun i ↦ -Ideal.Quotient.mk I (MvPolynomial.X i)) (relation p α) = 0
        rw [eval_relation]
        have hneg0 :
            (-(Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))))) ^ p =
              (-1) ^ p * Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))) ^ p := by
          exact neg_pow
            (Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2)))) p
        have hneg1 :
            (-(Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))))) ^ p =
              (-1) ^ p * Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))) ^ p := by
          exact neg_pow
            (Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2)))) p
        rw [hneg0, hneg1]
        have hrel' :
            Ideal.Quotient.mk I
                (MvPolynomial.X (ULift.up (0 : Fin 2)) ^ p +
                  MvPolynomial.C α * MvPolynomial.X (ULift.up (1 : Fin 2)) ^ p) =
              (0 : Ring p α) := by
          simpa [I, relation] using quotient_relation_eq_zero (k := k) p α
        have hC :
            Ideal.Quotient.mk I (MvPolynomial.C α) = algebraMap k (Ring p α) α := by
          rfl
        have hrel :
            Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))) ^ p +
                algebraMap k (Ring p α) α *
                  Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))) ^ p =
              (0 : Ring p α) := by
          simpa [map_add, map_mul, map_pow, hC] using hrel'
        calc
          (-1) ^ p * Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))) ^ p +
              algebraMap k (Ring p α) α *
                ((-1) ^ p * Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))) ^ p)
            = (-1) ^ p *
                (Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (0 : Fin 2))) ^ p +
                  algebraMap k (Ring p α) α *
                    Ideal.Quotient.mk I (MvPolynomial.X (ULift.up (1 : Fin 2))) ^ p) := by
                ring_nf
          _ = 0 := by rw [hrel, mul_zero]
      rw [map_mul, hψ, zero_mul]
  Spec.map (CommRingCat.ofHom ψbar)

/-- The lifted unit composes with the quotient inclusion to evaluation at zero. -/
theorem oneLeft_comp_inclusionToSpec [Fact p.Prime] :
    oneLeft p α ≫ inclusionToSpec p α =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => (0 : k)))) := by
  dsimp only [oneLeft, inclusionToSpec]
  change (Spec.map _ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Ring p α))) ≫
    (Spec.map _ : Spec (CommRingCat.of (Ring p α)) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

/-- The lifted inverse composes with the quotient inclusion to coordinatewise negation. -/
theorem invLeft_comp_inclusionToSpec :
    invLeft p α ≫ inclusionToSpec p α =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k (Ring p α))
        (fun i => -Ideal.Quotient.mk
          (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))) (MvPolynomial.X i)))) := by
  dsimp only [invLeft, inclusionToSpec]
  change (Spec.map _ : Spec (CommRingCat.of (Ring p α)) ⟶ Spec (CommRingCat.of (Ring p α))) ≫
    (Spec.map _ : Spec (CommRingCat.of (Ring p α)) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k))) = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.lift_comp_mk]

/-- The lifted addition has the prescribed quotient-presentation composite. -/
theorem mulLeft_comp_inclusionToSpec [Fact p.Prime] [CharP k p] :
    mulLeft p α ≫ inclusionToSpec p α =
      ((inclusion p α ⊗ₘ inclusion p α) ≫ μ[ambient]).left ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k)).hom := by
  exact Scheme.Hom.liftQuotient_comp _ _ _

/-- The lifted addition composes with the inclusion to ambient addition. -/
theorem mulLeft_comp_inclusion [Fact p.Prime] [CharP k p] :
    mulLeft p α ≫ (inclusion p α).left =
      ((inclusion p α ⊗ₘ inclusion p α) ≫ μ[ambient]).left := by
  change mulLeft p α ≫ (inclusionToSpec p α ≫ _) = _
  rw [← Category.assoc, mulLeft_comp_inclusionToSpec, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The unit morphism of the p-th-power kernel over `Spec k`. -/
def oneHom [Fact p.Prime] :
    𝟙_ (Over (Spec (CommRingCat.of.{u} k))) ⟶ over p α :=
  Over.homMk (oneLeft p α) (by
    dsimp only [oneLeft]
    change (Spec.map _ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Ring p α))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α))) = 𝟙 (Spec (CommRingCat.of k))
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_id,
      RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    rw [← Ideal.Quotient.mk_algebraMap k
      (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))) x]
    simp)

/-- The multiplication morphism of the p-th-power kernel over `Spec k`. -/
def mulHom [Fact p.Prime] [CharP k p] :
    over p α ⊗ over p α ⟶ over p α :=
  Over.homMk (mulLeft p α) (by
    calc
      mulLeft p α ≫ (over p α).hom =
          (mulLeft p α ≫ (inclusion p α).left) ≫ ambient.hom :=
        (congrArg (fun f => mulLeft p α ≫ f) (Over.w (inclusion p α)).symm).trans
          (Category.assoc _ _ _).symm
      _ = ((inclusion p α ⊗ₘ inclusion p α) ≫ μ[ambient]).left ≫ ambient.hom :=
        congrArg (fun f => f ≫ ambient.hom) (mulLeft_comp_inclusion p α)
      _ = (over p α ⊗ over p α).hom := Over.w _)

/-- The inverse morphism of the p-th-power kernel over `Spec k`. -/
def invHom :
    over p α ⟶ over p α :=
  Over.homMk (invLeft p α) (by
    dsimp only [invLeft]
    change (Spec.map _ : Spec (CommRingCat.of (Ring p α)) ⟶ Spec (CommRingCat.of (Ring p α))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α))) =
        Spec.map (CommRingCat.ofHom (algebraMap k (Ring p α)))
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.coe_comp, Function.comp_apply]
    nth_rw 1 [← Ideal.Quotient.mk_algebraMap k
      (Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))) x]
    simp)

/-- The closed immersion of the p-th-power kernel is a monomorphism over the base. -/
instance inclusion_mono : Mono (inclusion p α) :=
  Over.mono_of_mono_left (inclusion p α)

variable [Fact p.Prime] [CharP k p]

/-- The explicit factorization of the ambient additive operations through the p-th-power
kernel. -/
def factorization :
    GrpObj.Factorization (inclusion p α) where
  one := oneHom p α
  mul := mulHom p α
  inv := invHom p α
  one_hom := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · exact (Over.w (oneHom p α ≫ inclusion p α)).trans (Over.w η[ambient]).symm
    · intro i
      let P := CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)
      let φ : P ⟶ CommRingCat.of k :=
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ => (0 : k)))
      calc
        (oneHom p α ≫ inclusion p α).left.appTop (coord (Spec (CommRingCat.of k)) i) =
            (oneLeft p α ≫ inclusionToSpec p α).appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i)) :=
          congrArg (fun r => (oneLeft p α ≫ inclusionToSpec p α).appTop r)
            (AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of k) i)
        _ = (Spec.map φ).appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i)) :=
          congrArg (fun f : Spec (CommRingCat.of k) ⟶ Spec P =>
            f.appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i))) (oneLeft_comp_inclusionToSpec p α)
        _ = (Scheme.ΓSpecIso (CommRingCat.of k)).inv (φ (MvPolynomial.X i)) :=
          congrArg (fun h : P ⟶ Γ(Spec (CommRingCat.of k), ⊤) => h (MvPolynomial.X i))
            (Scheme.ΓSpecIso_inv_naturality φ).symm
        _ = 0 := by
          change (Scheme.ΓSpecIso (CommRingCat.of k)).inv
            (MvPolynomial.eval₂ (RingHom.id k) (fun _ => (0 : k)) (MvPolynomial.X i)) = 0
          rw [MvPolynomial.eval₂_X, map_zero]
        _ = _ := (AffineSpace.homOfVector_appTop_coord (𝟙 (Spec (CommRingCat.of k)))
          (fun _ : ULift.{u} (Fin 2) => (0 : Γ(Spec (CommRingCat.of k), ⊤))) i).symm
  mul_hom := by
    apply Over.OverMorphism.ext
    exact mulLeft_comp_inclusion p α
  inv_hom := by
    apply Over.OverMorphism.ext
    apply AffineSpace.hom_ext
    · exact (Over.w (invHom p α ≫ inclusion p α)).trans
        (Over.w (inclusion p α ≫ ι[ambient])).symm
    · intro i
      let P := CommRingCat.of (MvPolynomial (ULift.{u} (Fin 2)) k)
      let I := Ideal.span ({relation p α} : Set (MvPolynomial (ULift.{u} (Fin 2)) k))
      let φ : P ⟶ CommRingCat.of (Ring p α) :=
        CommRingCat.ofHom (MvPolynomial.eval₂Hom (algebraMap k (Ring p α))
          (fun i => -Ideal.Quotient.mk I (MvPolynomial.X i)))
      let J : Spec (CommRingCat.of (Ring p α)) ⟶ 𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) :=
        inclusionToSpec p α ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 2)) (CommRingCat.of k)).inv
      let V : Spec (CommRingCat.of (Ring p α)) ⟶ Spec (CommRingCat.of (Ring p α)) := invLeft p α
      let f : Spec (CommRingCat.of (Ring p α)) ⟶ Spec P := invLeft p α ≫ inclusionToSpec p α
      change (V ≫ J).appTop (coord (Spec (CommRingCat.of k)) i) =
        (J ≫ AffineSpace.negLeft _ _).appTop (coord (Spec (CommRingCat.of k)) i)
      calc
        (V ≫ J).appTop (coord (Spec (CommRingCat.of k)) i) =
            f.appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i)) :=
          congrArg (fun r => f.appTop r)
            (AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of k) i)
        _ = (Spec.map φ).appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i)) :=
          congrArg (fun f : Spec (CommRingCat.of (Ring p α)) ⟶ Spec P =>
            f.appTop ((Scheme.ΓSpecIso P).inv (MvPolynomial.X i))) (invLeft_comp_inclusionToSpec p α)
        _ = (Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv (φ (MvPolynomial.X i)) :=
          congrArg (fun h : P ⟶ Γ(Spec (CommRingCat.of (Ring p α)), ⊤) => h (MvPolynomial.X i))
            (Scheme.ΓSpecIso_inv_naturality φ).symm
        _ = -((Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv
            (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
          change (Scheme.ΓSpecIso (CommRingCat.of (Ring p α))).inv
            (MvPolynomial.eval₂ (algebraMap k (Ring p α))
              (fun j => -Ideal.Quotient.mk I (MvPolynomial.X j)) (MvPolynomial.X i)) = _
          rw [MvPolynomial.eval₂_X, map_neg]
        _ = -(J.appTop (coord (Spec (CommRingCat.of k)) i)) :=
          congrArg (fun r : Γ(Spec (CommRingCat.of (Ring p α)), ⊤) => -r)
            (inclusion_appTop_coord p α i).symm
        _ = (J ≫ AffineSpace.negLeft _ _).appTop (coord (Spec (CommRingCat.of k)) i) := by
          symm
          calc
            _ = J.appTop (-(coord (Spec (CommRingCat.of k)) i)) :=
              congrArg (fun r => J.appTop r)
                (AffineSpace.homOfVector_appTop_coord
                  (𝔸(ULift.{u} (Fin 2); Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
                  (fun j => -(coord (Spec (CommRingCat.of k)) j)) i)
            _ = _ := map_neg J.appTop.hom _

/-- The group-object structure induced by the factored affine-plane operations. -/
instance instGrpObjOver : GrpObj (over p α) :=
  (factorization p α).toGrpObj

/-- The inclusion into the affine plane preserves the induced group operations. -/
instance inclusion_isMonHom : IsMonHom (inclusion p α) :=
  { one_hom := (factorization p α).one_hom
    mul_hom := (factorization p α).mul_hom }

end GroupStructure

/-- The closed additive subgroup scheme `V(X₀ ^ p + α * X₁ ^ p)` of the affine plane. -/
noncomputable abbrev closedSubgroup (p : ℕ) [Fact p.Prime]
    {k : Type u} [CommRing k] [CharP k p] (α : k) :
    Scheme.ClosedSubgroup (ambient : Over (Spec (CommRingCat.of.{u} k))) :=
  (factorization p α).toClosedSubgroup

/-- The inclusion carried by `closedSubgroup p α` is the quotient-presentation inclusion. -/
theorem closedSubgroup_inclusion (p : ℕ) [Fact p.Prime]
    {k : Type u} [CommRing k] [CharP k p] (α : k) :
    HEq (closedSubgroup p α).inclusion (inclusion p α) := by
  simpa [closedSubgroup] using
    (GrpObj.Factorization.toClosedSubgroup_inclusion (factorization p α))

/-- A homogeneous p-th-power kernel with a non-p-th-power coefficient is integral. -/
theorem isIntegral (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsIntegral (scheme p α) := by
  letI := MvPolynomial.PthPowerKernel.isDomain p α hα
  exact (affine_isIntegral_iff (CommRingCat.of (Ring p α))).mpr inferInstance

/-- A non-p-th-power coefficient canonically supplies integrality of the corresponding kernel. -/
instance instIsIntegralOfNotPthPower (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p] (α : k)
    [hα : Fact (α ∉ Set.range (fun β : k ↦ β ^ p))] :
    IsIntegral (scheme p α) :=
  isIntegral p α hα.out

/-- The structure morphism of a homogeneous p-th-power kernel with a non-p-th-power
coefficient is not smooth. -/
theorem notSmooth (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    ¬ Smooth (toBase p α) := sorry

/-- A homogeneous p-th-power kernel with a non-p-th-power coefficient is not normal. -/
theorem notNormal (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    ¬ (scheme p α).isNormal := sorry

/-- A homogeneous p-th-power kernel with a non-p-th-power coefficient is reduced. -/
theorem isReduced (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IsReduced (scheme p α) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced (scheme p α)).mp (isIntegral p α hα) |>.2

/-- A homogeneous p-th-power kernel with a non-p-th-power coefficient is irreducible. -/
theorem irreducibleSpace (p : ℕ) [Fact p.Prime]
    {k : Type u} [Field k] [CharP k p]
    (α : k) (hα : α ∉ Set.range (fun β : k ↦ β ^ p)) :
    IrreducibleSpace (scheme p α) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced (scheme p α)).mp (isIntegral p α hα) |>.1

end AlgebraicGeometry.PthPowerKernel
