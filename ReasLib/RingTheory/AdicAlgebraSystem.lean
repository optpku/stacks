/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.CategoryTheory.InverseSystem.Positive

/-!
# Adic inverse systems of algebras

For a commutative ring `A` and ideal `I`, the inverse system `n ↦ A ⧸ I ^ n` is the
base of the category of finite-type adic inverse systems of algebras: objects are
inverse systems `⋯ ⟶ B₃ ⟶ B₂ ⟶ B₁` in which each `B n` is a finite-type
`A ⧸ I ^ n`-algebra and each successor map `B (n + 1) ⟶ B n` is an
`A ⧸ I ^ (n + 1)`-algebra homomorphism inducing `B (n + 1) ⧸ I ^ n B (n + 1) ≅ B n`.
Morphisms are systems of ring homomorphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.PNatInverseSystem

universe u

namespace AdicAlgebraSystem

variable {A : Type u} [CommRing A]

/-- Quotient powers are compatible with morphisms in `OrderDual ℕ+`. -/
theorem pow_le_of_orderDual_hom (I : Ideal A) {i j : OrderDual ℕ+} (f : i ⟶ j) :
    I ^ ((OrderDual.ofDual i : ℕ+) : ℕ) ≤ I ^ ((OrderDual.ofDual j : ℕ+) : ℕ) := by
  exact Ideal.pow_le_pow_right (show ((OrderDual.ofDual j : ℕ+) : ℕ) ≤
    ((OrderDual.ofDual i : ℕ+) : ℕ) from leOfHom f)

/-- The quotient-factor map associated to an identity is the identity of the quotient ring. -/
theorem quotientSystem_map_id (I : Ideal A) (i : OrderDual ℕ+) :
    CommRingCat.ofHom (Ideal.Quotient.factor (pow_le_of_orderDual_hom I (𝟙 i))) =
      𝟙 (CommRingCat.of (A ⧸ I ^ ((OrderDual.ofDual i : ℕ+) : ℕ))) := by
  apply CommRingCat.hom_ext
  exact Ideal.Quotient.factor_eq

/-- Quotient-factor maps compose along morphisms of positive order-dual indices. -/
theorem quotientSystem_map_comp (I : Ideal A) {i j k : OrderDual ℕ+}
    (f : i ⟶ j) (g : j ⟶ k) :
    CommRingCat.ofHom (Ideal.Quotient.factor (pow_le_of_orderDual_hom I (f ≫ g))) =
      CommRingCat.ofHom (Ideal.Quotient.factor (pow_le_of_orderDual_hom I f)) ≫
        CommRingCat.ofHom (Ideal.Quotient.factor (pow_le_of_orderDual_hom I g)) := by
  apply CommRingCat.hom_ext
  exact (Ideal.Quotient.factor_comp
    (pow_le_of_orderDual_hom I f) (pow_le_of_orderDual_hom I g)).symm

/-- The inverse system `n ↦ A ⧸ I ^ n` of adic quotient rings. -/
def quotientSystem (I : Ideal A) : PNatInverseSystem CommRingCat.{u} where
  obj i := CommRingCat.of (A ⧸ I ^ ((OrderDual.ofDual i : ℕ+) : ℕ))
  map f := CommRingCat.ofHom (Ideal.Quotient.factor (pow_le_of_orderDual_hom I f))
  map_id := quotientSystem_map_id I
  map_comp := quotientSystem_map_comp I

/-- The stage of `quotientSystem I` at `n` is `A ⧸ I ^ n`. -/
theorem quotientSystem_stage (I : Ideal A) (n : ℕ+) :
    (quotientSystem I).stage n = CommRingCat.of (A ⧸ I ^ (n : ℕ)) := rfl

/-- The `A ⧸ I ^ n`-algebra structure on a system of algebras over the adic quotient tower. -/
instance instAlgebraStage (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    Algebra (A ⧸ I ^ (n : ℕ)) (B.right.stage n) :=
  (B.hom.app (OrderDual.toDual n)).hom.toAlgebra

/-- The structure map `A ⧸ I ^ n →+* B n` of an inverse system of algebras. -/
def stageAlgebraMap (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    A ⧸ I ^ (n : ℕ) →+* B.right.stage n :=
  (B.hom.app (OrderDual.toDual n)).hom

/-- The `A`-algebra structure on each stage, via `A → A ⧸ I ^ n → B n`. -/
instance instAlgebra (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    Algebra A (B.right.stage n) :=
  ((stageAlgebraMap I B n).comp (Ideal.Quotient.mk (I ^ (n : ℕ)))).toAlgebra

/-- Evaluating `stageAlgebraMap` on a residue class is the `A`-algebra structure map. -/
theorem stageAlgebraMap_mk (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) (a : A) :
    stageAlgebraMap I B n (Ideal.Quotient.mk (I ^ (n : ℕ)) a) =
      algebraMap A (B.right.stage n) a := rfl

/-- The successor transition `B (n + 1) →+* B n`. -/
def stepRingHom (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    B.right.stage (n + 1) →+* B.right.stage n :=
  (stepMap B.right n).hom

/-- Successor maps of an `Under (quotientSystem I)` object are `A ⧸ I ^ (n + 1)`-algebra maps. -/
theorem stepRingHom_comp_stageAlgebraMap (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    (stepRingHom I B n).comp (stageAlgebraMap I B (n + 1)) =
      (stageAlgebraMap I B n).comp
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n : ℕ)))) := by
  exact (congrArg (fun f ↦ f.hom)
    (B.hom.naturality
      (homOfLE (OrderDual.toDual_le_toDual.mpr (PNat.lt_succ_self n).le)))).symm

/-- The successor map annihilates the extension of `I ^ n` to stage `n + 1`. -/
theorem stepRingHom_eq_zero_of_mem_map_pow (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+)
    {x : B.right.stage (n + 1)}
    (hx : x ∈ (I ^ (n : ℕ)).map (algebraMap A (B.right.stage (n + 1)))) :
    stepRingHom I B n x = 0 := by
  have hle : (I ^ (n : ℕ)).map (algebraMap A (B.right.stage (n + 1))) ≤
      RingHom.ker (stepRingHom I B n) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change stepRingHom I B n (algebraMap A (B.right.stage (n + 1)) a) = 0
    rw [← stageAlgebraMap_mk I B (n + 1)]
    change ((stepRingHom I B n).comp (stageAlgebraMap I B (n + 1)))
      (Ideal.Quotient.mk _ a) = 0
    rw [stepRingHom_comp_stageAlgebraMap]
    change stageAlgebraMap I B n (Ideal.Quotient.mk _ a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  exact RingHom.mem_ker.mp (hle hx)

/-- The canonical comparison `B (n + 1) ⧸ I ^ n B (n + 1) →+* B n`. -/
def stepQuotientHom (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+) :
    B.right.stage (n + 1) ⧸ (I ^ (n : ℕ)).map (algebraMap A (B.right.stage (n + 1))) →+*
      B.right.stage n :=
  Ideal.Quotient.lift ((I ^ (n : ℕ)).map (algebraMap A (B.right.stage (n + 1))))
    (stepRingHom I B n) fun _ hx ↦ stepRingHom_eq_zero_of_mem_map_pow I B n hx

/-- `stepQuotientHom` recovers `stepRingHom` on residue classes. -/
theorem stepQuotientHom_mk (I : Ideal A) (B : Under (quotientSystem I)) (n : ℕ+)
    (x : B.right.stage (n + 1)) :
    stepQuotientHom I B n
        (Ideal.Quotient.mk ((I ^ (n : ℕ)).map (algebraMap A (B.right.stage (n + 1)))) x) =
      stepRingHom I B n x := rfl

/-- An inverse system over `quotientSystem I` lies in the restricted category when each stage is
of finite type and each successor map induces `B (n + 1) ⧸ I ^ n B (n + 1) ≅ B n`. -/
class IsObject (I : Ideal A) (B : Under (quotientSystem I)) : Prop where
  /-- Each stage `B n` is a finite-type `A ⧸ I ^ n`-algebra. -/
  finiteType_stage : ∀ n, (stageAlgebraMap I B n).FiniteType
  /-- Each successor map induces a bijection `B (n + 1) ⧸ I ^ n B (n + 1) ≅ B n`. -/
  bijective_stepQuotientHom : ∀ n, Function.Bijective (stepQuotientHom I B n)

/-- Build `IsObject` from finite type of all stages and bijectivity of the induced
successor quotients. -/
theorem IsObject.ofFiniteTypeBijective {I : Ideal A} {B : Under (quotientSystem I)}
    (hft : ∀ n, (stageAlgebraMap I B n).FiniteType)
    (hiso : ∀ n, Function.Bijective (stepQuotientHom I B n)) :
    IsObject I B := ⟨hft, hiso⟩

/-- The identity system `n ↦ A ⧸ I ^ n` satisfies the object conditions. -/
instance instIsObjectQuotientSystem (I : Ideal A) :
    IsObject I (Under.mk (𝟙 (quotientSystem I))) := by
  refine ⟨?_, ?_⟩
  · intro n
    exact RingHom.FiniteType.id _
  · intro n
    have h : stepQuotientHom I (Under.mk (𝟙 (quotientSystem I))) n =
        (DoubleQuot.quotQuotEquivQuotOfLE
          (Ideal.pow_le_pow_right (Nat.le_succ (n : ℕ)))).toRingHom := by
      apply Ideal.Quotient.ringHom_ext
      apply Ideal.Quotient.ringHom_ext
      ext a
      rfl
    rw [h]
    exact (DoubleQuot.quotQuotEquivQuotOfLE
      (Ideal.pow_le_pow_right (Nat.le_succ (n : ℕ)))).bijective

/-- Stages of an `IsObject` system are finite-type over `A ⧸ I ^ n` via `stageAlgebraMap`. -/
theorem finiteType_stage {I : Ideal A} {B : Under (quotientSystem I)} [IsObject I B] (n : ℕ+) :
    (stageAlgebraMap I B n).FiniteType := IsObject.finiteType_stage n

namespace IsObject

variable {I : Ideal A} {B : Under (quotientSystem I)}

/-- Membership in the restricted category is finite type of stages together with bijectivity of
the induced successor quotients. -/
theorem iff :
    IsObject I B ↔
      (∀ n, (stageAlgebraMap I B n).FiniteType) ∧
        ∀ n, Function.Bijective (stepQuotientHom I B n) :=
  ⟨fun h ↦ ⟨h.finiteType_stage, h.bijective_stepQuotientHom⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An `IsObject` system has finite-type stages and bijective induced successor quotients. -/
theorem spec [IsObject I B] :
    (∀ n, (stageAlgebraMap I B n).FiniteType) ∧
      ∀ n, Function.Bijective (stepQuotientHom I B n) :=
  ⟨IsObject.finiteType_stage, IsObject.bijective_stepQuotientHom⟩

end IsObject

/-- Finite type of the structure map yields `Algebra.FiniteType` on the stage. -/
instance finiteType_stage_algebra {I : Ideal A} (B : Under (quotientSystem I)) [IsObject I B]
    (n : ℕ+) : Algebra.FiniteType (A ⧸ I ^ (n : ℕ)) (B.right.stage n) :=
  finiteType_stage n

/-- The object property of finite-type adic inverse systems of algebras over `I`. -/
abbrev isObject (I : Ideal A) : ObjectProperty (Under (quotientSystem I)) :=
  fun B ↦ IsObject I B

/-- Unfolding `isObject` recovers `IsObject`. -/
theorem isObject_iff (I : Ideal A) (B : Under (quotientSystem I)) :
    isObject I B ↔ IsObject I B := Iff.rfl

end AdicAlgebraSystem

/-- The category of inverse systems `⋯ ⟶ B₃ ⟶ B₂ ⟶ B₁` where each `B n` is a finite-type
`A ⧸ I ^ n`-algebra and each transition `B (n + 1) ⟶ B n` is an `A ⧸ I ^ (n + 1)`-algebra
map inducing `B (n + 1) ⧸ I ^ n B (n + 1) ≅ B n`. Morphisms are systems of homomorphisms. -/
abbrev AdicAlgebraSystem (A : Type u) [CommRing A] (I : Ideal A) :=
  (AdicAlgebraSystem.isObject I).FullSubcategory

namespace AdicAlgebraSystem

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- Bundle a finite-type adic inverse system of algebras as an object of
`AdicAlgebraSystem A I`. -/
@[simps obj]
abbrev of (B : Under (quotientSystem I)) [IsObject I B] : AdicAlgebraSystem A I where
  obj := B
  property := ‹_›

/-- The inclusion of finite-type adic inverse systems of algebras into all inverse systems of
algebras over `quotientSystem I`. -/
abbrev inclusion : AdicAlgebraSystem A I ⥤ Under (quotientSystem I) :=
  (isObject I).ι

/-- The inclusion sends an object to its underlying inverse system. -/
theorem inclusion_obj (B : AdicAlgebraSystem A I) : (inclusion A I).obj B = B.obj := rfl

/-- An object of `AdicAlgebraSystem A I` satisfies `IsObject`. -/
instance instIsObjectObj (B : AdicAlgebraSystem A I) : IsObject I B.obj :=
  B.property

variable {A I}

/-- Construct a morphism in `AdicAlgebraSystem A I` from a morphism of underlying systems. -/
abbrev ofHom {B B' : Under (quotientSystem I)} [IsObject I B] [IsObject I B'] (f : B ⟶ B') :
    of A I B ⟶ of A I B' :=
  ObjectProperty.homMk f

/-- The underlying morphism of `ofHom f` is `f`. -/
theorem ofHom_hom {B B' : Under (quotientSystem I)} [IsObject I B] [IsObject I B'] (f : B ⟶ B') :
    (ofHom f).hom = f := rfl

variable (I)

/-- The identity system `n ↦ A ⧸ I ^ n` as an object of `AdicAlgebraSystem A I`. -/
def ofQuotientSystem : AdicAlgebraSystem A I :=
  of A I (Under.mk (𝟙 (quotientSystem I)))

/-- The underlying system of `ofQuotientSystem I` is the identity system on `quotientSystem I`. -/
theorem ofQuotientSystem_obj :
    (ofQuotientSystem I).obj = Under.mk (𝟙 (quotientSystem I)) := rfl

end AdicAlgebraSystem
