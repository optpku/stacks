module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.Algebra.MonoidAlgebra.Lift
public import Mathlib.Algebra.Group.Commute.Units
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter

/-!
# Cyclotomic Tate twists of finite-ring modules

The cyclotomic character acts by central prime-ring scalars.
-/

@[expose] public section

open CategoryTheory
open scoped MonoidAlgebra

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme.Etale

variable {Λ : Type (u + 1)} [Ring Λ] [Finite Λ]

/-- A finite ring has nonzero cardinality. -/
theorem natCard_ne_zero_of_finite_ring : NeZero (Nat.card Λ) :=
  ⟨by
    have : Nonempty Λ := ⟨0⟩
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩

/-- Finite rings have nonzero cardinality, as a typeclass instance. -/
instance instNeZero_natCard : NeZero (Nat.card Λ) :=
  natCard_ne_zero_of_finite_ring

/-- In a finite ring, the cardinality annihilates the additive group. -/
theorem finite_ring_cast_card_eq_zero : (Nat.card Λ : Λ) = 0 :=
  sorry

/-- The unique ring homomorphism `ZMod (Nat.card Λ) →+* Λ` induced by `n • 1 = 0`. -/
def zmodCardRingHom : ZMod (Nat.card Λ) →+* Λ :=
  (Ideal.Quotient.lift (Ideal.span {(Nat.card Λ : ℤ)}) (Int.castRingHom Λ)
      sorry).comp
    (Int.quotientSpanNatEquivZMod (Nat.card Λ)).symm.toRingHom

/-- The prime-ring image is central even when the coefficient ring is noncommutative. -/
theorem zmodCardRingHom_commute (a : ZMod (Nat.card Λ)) (r : Λ) :
    Commute (zmodCardRingHom a) r := by
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective a
  simpa only [map_intCast] using Int.cast_commute n r

/-- The group homomorphism sending a Galois element to its underlying ring automorphism. -/
def galoisToRingAut (k : Type u) [Field k] :
    Gal(AlgebraicClosure k/k) →* (AlgebraicClosure k ≃+* AlgebraicClosure k) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' := sorry

/-- Invertibility of `Nat.card Λ` in `k` implies that `k̄` contains exactly `n` nth roots of unity. -/
theorem rootsOfUnity_card_eq (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Nat.card { x // x ∈ rootsOfUnity (Nat.card Λ) (AlgebraicClosure k) } =
      Nat.card Λ :=
  sorry

/-- The finite-level cyclotomic character valued in `Λˣ`, obtained by composing
`modularCyclotomicCharacter` with the unique map from `ZMod n` into the finite ring `Λ`. -/
def cyclotomicCharacterMod (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) :
    Gal(AlgebraicClosure k/k) →* Λˣ :=
  (Units.map (zmodCardRingHom (Λ := Λ)).toMonoidHom).comp <|
    (modularCyclotomicCharacter (AlgebraicClosure k)
        (rootsOfUnity_card_eq (Λ := Λ) k hΛ)).comp
      (galoisToRingAut k)

/-- Cyclotomic scalars lie in the central prime-ring image. -/
theorem cyclotomicCharacterMod_commute (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) (σ : Gal(AlgebraicClosure k/k)) (r : Λ) :
    Commute (cyclotomicCharacterMod (Λ := Λ) k hΛ σ : Λ) r :=
  zmodCardRingHom_commute _ r

/-- Evaluating the finite-level cyclotomic character recovers the image of the modular
cyclotomic character in `Λ`. -/
theorem cyclotomicCharacterMod_apply (k : Type u) [Field k]
    (hΛ : IsUnit (Nat.card Λ : k)) (σ : Gal(AlgebraicClosure k/k)) :
    (cyclotomicCharacterMod (Λ := Λ) k hΛ σ : Λ) =
      zmodCardRingHom
        (modularCyclotomicCharacter (AlgebraicClosure k)
            (rootsOfUnity_card_eq (Λ := Λ) k hΛ)
          (galoisToRingAut k σ)) :=
  sorry

variable {G : Type v} [Group G]

/-- Scalar multiplications as additive endomorphisms of the underlying module. -/
def scalarToAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : Λ →+* AddMonoid.End M.V where
  toFun r := DistribSMul.toAddMonoidHom M.V r
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The additive endomorphism underlying a linear `G`-action. -/
def actionToAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : G →* AddMonoid.End M.V where
  toFun g := (M.ρ g).hom.toAddMonoidHom
  map_one' := sorry
  map_mul' := sorry

/-- The monoid-algebra representation on additive endomorphisms associated to a linear action. -/
def actionToMonoidAlgebraAddEnd (M : Action (ModuleCat.{max (u + 1) v} Λ) G) :
    Λ[G] →+* AddMonoid.End M.V :=
  MonoidAlgebra.liftNCRingHom (scalarToAddEnd M) (actionToAddEnd M) fun _ _ ↦ sorry

/-- The left `Λ[G]`-module structure on the underlying module of a linear `G`-action. -/
instance moduleOfAction (M : Action (ModuleCat.{max (u + 1) v} Λ) G) : Module (Λ[G]) M.V :=
  Module.compHom M.V (actionToMonoidAlgebraAddEnd M)

/-- Multiplication by a central unit of `Λ` as a `Λ`-linear endomorphism. -/
def unitsSMulEnd {P : Type w} [AddCommGroup P] [Module Λ P] (u : Λˣ)
    (hu : ∀ r : Λ, Commute (u : Λ) r) :
    Module.End Λ P where
  toFun p := (u : Λ) • p
  map_add' := fun x y ↦ smul_add (u : Λ) x y
  map_smul' := fun r p ↦ by
    simpa only [RingHom.id_apply, smul_smul] using congrArg (fun a : Λ ↦ a • p) (hu r).eq

/-- Tate twist of a linear Gal(k̄/k)-action: `σ` acts by `χ(σ)⁻¹ • ρ(σ)`. -/
def tateTwist {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) :
    Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k) where
  V := M.V
  ρ :=
    { toFun := fun σ ↦
        ModuleCat.ofHom
            ((unitsSMulEnd (cyclotomicCharacterMod (Λ := Λ) k hΛ σ)⁻¹
              (fun r ↦ (cyclotomicCharacterMod_commute k hΛ σ r).units_inv_left)).comp
                (M.ρ σ).hom)
      map_one' := sorry
      map_mul' := sorry }

/-- The underlying module of a Tate twist is unchanged. -/
theorem tateTwist_V {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k)) :
    (tateTwist hΛ M).V = M.V :=
  rfl

/-- Evaluating the Tate-twisted action inserts the inverse cyclotomic scalar. -/
theorem tateTwist_ρ {k : Type u} [Field k] (hΛ : IsUnit (Nat.card Λ : k))
    (M : Action (ModuleCat.{u + 1} Λ) Gal(AlgebraicClosure k/k))
    (σ : Gal(AlgebraicClosure k/k)) :
    (tateTwist hΛ M).ρ σ =
      ModuleCat.ofHom
        ((unitsSMulEnd (cyclotomicCharacterMod (Λ := Λ) k hΛ σ)⁻¹
          (fun r ↦ (cyclotomicCharacterMod_commute k hΛ σ r).units_inv_left)).comp
            (M.ρ σ).hom) :=
  rfl

end AlgebraicGeometry.Scheme.Etale
