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
    (by sorry)

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
    (by sorry)

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

/-- The unit morphism of the p-th-power kernel over `Spec k`. -/
def oneHom [Fact p.Prime] :
    𝟙_ (Over (Spec (CommRingCat.of.{u} k))) ⟶ over p α :=
  Over.homMk (oneLeft p α) (by sorry)

/-- The multiplication morphism of the p-th-power kernel over `Spec k`. -/
def mulHom [Fact p.Prime] [CharP k p] :
    over p α ⊗ over p α ⟶ over p α :=
  Over.homMk (mulLeft p α) (by sorry)

/-- The inverse morphism of the p-th-power kernel over `Spec k`. -/
def invHom :
    over p α ⟶ over p α :=
  Over.homMk (invLeft p α) (by sorry)

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
  one_hom := by sorry
  mul_hom := by sorry
  inv_hom := by sorry

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
    IsIntegral (scheme p α) := sorry

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
