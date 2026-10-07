module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap88.Lemma_88_2_1_Limit
public import stacks_project.Chap88.«88_2_3_1_BaseChange»
public import stacks_project.Chap88.«88_2_3_2_BaseChange»

/-!
# Comparison of systems and completed base change

A ring map `A1 → A2` with `I1.map (algebraMap A1 A2) ^ c ≤ I2` for some `c ≥ 1`
induces both the systems functor of 88.2.3.1 and, when `I2` is finitely
generated, the completed functor of 88.2.3.2. This file supplies the stagewise
comparison maps and the natural isomorphism making the square with
`toAdicSystem` 2-commute.
-/

@[expose] public section

open CategoryTheory
open Algebra.TopologicallyFiniteType
open scoped TensorProduct

noncomputable section

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace CommAlgCat.TopologicallyFiniteType

open AdicAlgebraSystem (baseChangeHom stretchIndex tensorOverIncludeLeft
  tensorOverIncludeRight tensorOverLift stageAlgebraMap)

/-- Image-power containment is equivalent to the image of a power, matching the
two spellings of `φ(I1 ^ c) ⊆ I2`. -/
theorem map_le_map_pow (φ : A1 →+* A2) (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} :
    (Ideal.map φ I1) ^ c ≤ I2 ↔ Ideal.map φ (I1 ^ c) ≤ I2 := sorry

/-- The systems-base-change form of the completed-base-change containment. -/
theorem map_pow_le_of_map_pow (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) :
    Ideal.map (algebraMap A1 A2) (I1 ^ c) ≤ I2 := sorry

/-- The composite `B → B ⊗[A1] A2 → (B ⊗[A1] A2)^∧`. -/
def includeLeftToCompletion (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    B →+* completedBaseChange A1 I2 B :=
  (algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B)).comp
    Algebra.TensorProduct.includeLeftRingHom

/-- `includeLeftToCompletion` sends `b` to the class of `b ⊗ₜ 1` in the
completion. -/
theorem includeLeftToCompletion_apply (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] (b : B) :
    includeLeftToCompletion I2 B b =
      algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B) (b ⊗ₜ 1) := sorry

/-- The extended power `I1 ^ (c * n) B` lands in the comap of `I2 ^ n` along
`includeLeftToCompletion`. -/
theorem stageCompareLeft_le_comap (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2)
    (B : Type u) [CommRing B] [Algebra A1 B] (n : ℕ+) :
    (I1 ^ (stretchIndex hc n : ℕ)).map (algebraMap A1 B) ≤
      ((I2 ^ (n : ℕ)).map (algebraMap A2 (completedBaseChange A1 I2 B))).comap
        (includeLeftToCompletion I2 B) := sorry

/-- The stage map `B ⧸ I1 ^ (c * n) B → (B ⊗[A1] A2)^∧ ⧸ I2 ^ n (B ⊗[A1] A2)^∧`
induced by `includeLeftToCompletion`. -/
def stageCompareLeftHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    ((toAdicSystem I1).obj B).obj.right.stage (stretchIndex hc n) →+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  Ideal.quotientMap
    ((I2 ^ (n : ℕ)).map (algebraMap A2 ((baseChange I1 I2 hc hI hI2).obj B).obj))
    (includeLeftToCompletion I2 B.obj)
    (stageCompareLeft_le_comap I1 I2 hc hI B.obj n)

/-- `stageCompareLeftHom` is the quotient of `includeLeftToCompletion`. -/
theorem stageCompareLeftHom_mk (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+)
    (x : B.obj) :
    stageCompareLeftHom I1 I2 hc hI hI2 B n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (includeLeftToCompletion I2 B.obj x) := sorry

/-- The stage comparison homomorphism from the systems tensor
`B (c * n) ⊗[A1 ⧸ I1 ^ (c * n)] (A2 ⧸ I2 ^ n)` to the adic quotient of the
completed tensor. -/
def stageCompareHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    AdicAlgebraSystem.baseChangeStage (algebraMap A1 A2) I1 I2 hc
        (map_pow_le_of_map_pow I1 I2 hI) ((toAdicSystem I1).obj B).obj n →+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  tensorOverLift
    (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
    (baseChangeHom (algebraMap A1 A2) I1 I2 hc (map_pow_le_of_map_pow I1 I2 hI) n)
    (stageCompareLeftHom I1 I2 hc hI hI2 B n)
    (stageAlgebraMap I2 ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n)

/-- The left inclusion into the systems tensor is sent to `stageCompareLeftHom`. -/
theorem stageCompareHom_includeLeft (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareHom I1 I2 hc hI hI2 B n).comp
      (tensorOverIncludeLeft
        (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
        (baseChangeHom (algebraMap A1 A2) I1 I2 hc (map_pow_le_of_map_pow I1 I2 hI) n)) =
      stageCompareLeftHom I1 I2 hc hI hI2 B n := sorry

/-- The right inclusion into the systems tensor is sent to the stage structure
map of the completed system. -/
theorem stageCompareHom_includeRight (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareHom I1 I2 hc hI hI2 B n).comp
      (tensorOverIncludeRight
        (stageAlgebraMap I1 ((toAdicSystem I1).obj B).obj (stretchIndex hc n))
        (baseChangeHom (algebraMap A1 A2) I1 I2 hc (map_pow_le_of_map_pow I1 I2 hI) n)) =
      stageAlgebraMap I2
        ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj n := sorry

/-- The stage comparison homomorphism is a ring equivalence. -/
def stageCompareEquiv (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    AdicAlgebraSystem.baseChangeStage (algebraMap A1 A2) I1 I2 hc
        (map_pow_le_of_map_pow I1 I2 hI) ((toAdicSystem I1).obj B).obj n ≃+*
      ((toAdicSystem I2).obj ((baseChange I1 I2 hc hI hI2).obj B)).obj.right.stage n :=
  RingEquiv.ofBijective (stageCompareHom I1 I2 hc hI hI2 B n) sorry

/-- The underlying homomorphism of `stageCompareEquiv` is `stageCompareHom`. -/
theorem stageCompareEquiv_toRingHom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (stageCompareEquiv I1 I2 hc hI hI2 B n).toRingHom =
      stageCompareHom I1 I2 hc hI hI2 B n := sorry

/-- Objectwise isomorphism of adic systems comparing systems base change of
`toAdicSystem I1` with `toAdicSystem I2` of completed base change. -/
def baseChangeObjIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    (toAdicSystem I1 ⋙
        AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (map_pow_le_of_map_pow I1 I2 hI)).obj B ≅
      (baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2).obj B :=
  ObjectProperty.isoMk _
    (Under.isoMk
      (NatIso.ofComponents
        (fun i ↦
          (stageCompareEquiv I1 I2 hc hI hI2 B (OrderDual.ofDual i)).toCommRingCatIso)
        sorry)
      sorry)

/-- The right-leg component of `baseChangeObjIso` at stage `n` is
`stageCompareEquiv`. -/
theorem baseChangeObjIso_stage (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (Under.Hom.right (baseChangeObjIso I1 I2 hc hI hI2 B).hom.hom).app
        (OrderDual.toDual n) =
      (stageCompareEquiv I1 I2 hc hI hI2 B n).toCommRingCatIso.hom := sorry

/-- Natural isomorphism identifying systems base change of `toAdicSystem I1`
with `toAdicSystem I2` of completed base change. -/
def baseChangeToAdicSystemIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG) :
    toAdicSystem I1 ⋙
        AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (map_pow_le_of_map_pow I1 I2 hI) ≅
      baseChange I1 I2 hc hI hI2 ⋙ toAdicSystem I2 :=
  NatIso.ofComponents (baseChangeObjIso I1 I2 hc hI hI2) sorry

/-- Components of `baseChangeToAdicSystemIso` are `baseChangeObjIso`. -/
theorem baseChangeToAdicSystemIso_app (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    (baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B =
      baseChangeObjIso I1 I2 hc hI hI2 B := sorry

/-- Stage components of `baseChangeToAdicSystemIso` are `stageCompareEquiv`. -/
theorem baseChangeToAdicSystemIso_stage (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) (n : ℕ+) :
    (Under.Hom.right ((baseChangeToAdicSystemIso I1 I2 hc hI hI2).app B).hom.hom).app
        (OrderDual.toDual n) =
      (stageCompareEquiv I1 I2 hc hI hI2 B n).toCommRingCatIso.hom := sorry

/-- When both ideals are finitely generated, inverse limits transport the
comparison isomorphism to an identification of completed base change with
systems base change. -/
def baseChangeLimitIso (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI1 : I1.FG) (hI2 : I2.FG) :
    AdicAlgebraSystem.limitFunctor I1 hI1 ⋙ baseChange I1 I2 hc hI hI2 ≅
      AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
          (map_pow_le_of_map_pow I1 I2 hI) ⋙
        AdicAlgebraSystem.limitFunctor I2 hI2 :=
  let S :=
    AdicAlgebraSystem.baseChange (algebraMap A1 A2) I1 I2 hc
      (map_pow_le_of_map_pow I1 I2 hI)
  let Cplt := baseChange I1 I2 hc hI hI2
  let L1 := AdicAlgebraSystem.limitFunctor I1 hI1
  let L2 := AdicAlgebraSystem.limitFunctor I2 hI2
  let T1 := toAdicSystem I1
  let T2 := toAdicSystem I2
  let α := baseChangeToAdicSystemIso I1 I2 hc hI hI2
  (Functor.rightUnitor (L1 ⋙ Cplt)).symm ≪≫
    Functor.isoWhiskerLeft (L1 ⋙ Cplt) (AdicAlgebraSystem.limitFunctorUnitIso I2 hI2) ≪≫
    (Functor.associator (L1 ⋙ Cplt) T2 L2).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator L1 Cplt T2) L2 ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft L1 α.symm) L2 ≪≫
    Functor.isoWhiskerRight (Functor.associator L1 T1 S).symm L2 ≪≫
    Functor.associator (L1 ⋙ T1) S L2 ≪≫
    Functor.isoWhiskerRight (AdicAlgebraSystem.limitFunctorCounitIso I1 hI1) (S ⋙ L2) ≪≫
    Functor.leftUnitor (S ⋙ L2)

/-- Components of `baseChangeLimitIso` are the objectwise transported comparison. -/
theorem baseChangeLimitIso_app (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ}
    (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI1 : I1.FG)
    (hI2 : I2.FG) (B : AdicAlgebraSystem A1 I1) :
    ((baseChangeLimitIso I1 I2 hc hI hI1 hI2).app B).hom =
      (baseChangeLimitIso I1 I2 hc hI hI1 hI2).hom.app B := sorry

end CommAlgCat.TopologicallyFiniteType

