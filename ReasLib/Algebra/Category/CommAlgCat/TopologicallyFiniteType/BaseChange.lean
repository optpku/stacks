/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType
public import ReasLib.RingTheory.AdicCompletion.Map

@[expose] public section

noncomputable section

open CategoryTheory TensorProduct

open scoped TensorProduct

universe u

variable {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]

namespace Algebra.TopologicallyFiniteType

/-- The extension of an ideal of `A2` to `B ⊗[A1] A2` along `includeRight`. -/
def tensorExtensionIdeal (I2 : Ideal A2) (B : Type u) [CommRing B] [Algebra A1 B] :
    Ideal (B ⊗[A1] A2) :=
  I2.map (Algebra.TensorProduct.includeRight : A2 →ₐ[A1] B ⊗[A1] A2).toRingHom

/-- The adic completion of `B ⊗[A1] A2` along the extended ideal of `I2`. -/
abbrev completedBaseChange (A1 : Type u) {A2 : Type u} [CommRing A1] [CommRing A2]
    [Algebra A1 A2] (I2 : Ideal A2) (B : Type u) [CommRing B] [Algebra A1 B] : Type u :=
  AdicCompletion (tensorExtensionIdeal I2 B : Ideal (B ⊗[A1] A2)) (B ⊗[A1] A2)

/-- The canonical `A2`-algebra structure on completed base change. -/
instance instAlgebra (I2 : Ideal A2) (B : Type u) [CommRing B] [Algebra A1 B] :
    Algebra A2 (completedBaseChange A1 I2 B) :=
  ((algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B)).comp
    (Algebra.TensorProduct.includeRight : A2 →ₐ[A1] B ⊗[A1] A2).toRingHom).toAlgebra

/-- The completed base-change carrier is the corresponding adic completion. -/
theorem completedBaseChange_spec (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] :
    completedBaseChange A1 I2 B =
      AdicCompletion (tensorExtensionIdeal I2 B : Ideal (B ⊗[A1] A2)) (B ⊗[A1] A2) := sorry

/-- The structure map to completed base change factors through `includeRight`. -/
theorem completedBaseChange_algebraMap_eq (I2 : Ideal A2) (B : Type u)
    [CommRing B] [Algebra A1 B] (a : A2) :
    algebraMap A2 (completedBaseChange A1 I2 B) a =
      algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B)
        (Algebra.TensorProduct.includeRight a) := sorry

/-- An `A1`-algebra map sends powers of the extended ideal into the corresponding
extended ideal by comapping along the tensor-product map. -/
theorem tensorExtensionIdeal_map_le_comap (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') (n : ℕ) :
    tensorExtensionIdeal I2 B ^ n ≤
      (tensorExtensionIdeal I2 B' ^ n).comap
        (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  have he : (tensorExtensionIdeal I2 B).map
      (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom =
      tensorExtensionIdeal I2 B' := by
    unfold tensorExtensionIdeal
    rw [Ideal.map_map]
    have hc : (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom.comp
        (Algebra.TensorProduct.includeRight : A2 →ₐ[A1] B ⊗[A1] A2).toRingHom =
        (Algebra.TensorProduct.includeRight : A2 →ₐ[A1] B' ⊗[A1] A2).toRingHom := by
      ext a
      simp [Algebra.TensorProduct.includeRight]
    rw [hc]
  rw [he]

/-- The tensor-product map is adically continuous, with explicit exponent one.
This certificate is proved before any exponent is selected in the shared map. -/
theorem tensorMap_adicContinuous (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') :
    (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom.AdicContinuous
      (tensorExtensionIdeal I2 B) (tensorExtensionIdeal I2 B') := by
  refine ⟨1, ?_⟩
  apply Ideal.map_le_iff_le_comap.mpr
  simpa only [pow_one] using tensorExtensionIdeal_map_le_comap I2 f 1

/-- The finite-stage quotient map induced by an `A1`-algebra homomorphism. -/
def completedBaseChangeQuotientMap (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') (n : ℕ) :
    completedBaseChange A1 I2 B →+* B' ⊗[A1] A2 ⧸ tensorExtensionIdeal I2 B' ^ n :=
  (Ideal.quotientMap (tensorExtensionIdeal I2 B' ^ n)
      (Algebra.TensorProduct.map f (AlgHom.id A1 A2)).toRingHom
      (tensorExtensionIdeal_map_le_comap I2 f n)).comp
    (AdicCompletion.evalₐ (tensorExtensionIdeal I2 B : Ideal (B ⊗[A1] A2)) n).toRingHom

/-- The finite-stage quotient maps commute with the inverse-system transition maps. -/
theorem completedBaseChangeQuotientMap_compatible (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (tensorExtensionIdeal I2 B') hle).comp
        (completedBaseChangeQuotientMap I2 f n) =
      completedBaseChangeQuotientMap I2 f m := by
  have he (k : ℕ) : (tensorMap_adicContinuous I2 f).quotientMap k =
      completedBaseChangeQuotientMap I2 f k :=
    (tensorMap_adicContinuous I2 f).quotientMap_eq_of_pow_le k k
      (tensorExtensionIdeal_map_le_comap I2 f k)
  rw [← he n, ← he m]
  exact (tensorMap_adicContinuous I2 f).quotientMap_compatible hle

/-- The completed base-change algebra map induced by an `A1`-algebra homomorphism. -/
def completedBaseChangeMap (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') :
    completedBaseChange A1 I2 B →ₐ[A2] completedBaseChange A1 I2 B' where
  __ := (RingHom.AdicContinuous.completionAlgHom
    (tensorExtensionIdeal I2 B) (tensorExtensionIdeal I2 B')
    (Algebra.TensorProduct.map f (AlgHom.id A1 A2))
    (tensorMap_adicContinuous I2 f)).toRingHom
  commutes' a := by
    change (tensorMap_adicContinuous I2 f).completionMap
        (algebraMap (B ⊗[A1] A2) (completedBaseChange A1 I2 B)
          (Algebra.TensorProduct.includeRight a)) =
      algebraMap (B' ⊗[A1] A2) (completedBaseChange A1 I2 B')
        (Algebra.TensorProduct.includeRight a)
    simpa [Algebra.TensorProduct.includeRight] using
      RingHom.congr_fun (tensorMap_adicContinuous I2 f).completionMap_comp
        (Algebra.TensorProduct.includeRight a)

/-- The underlying map is the canonical completion of the tensor-product map. -/
theorem completedBaseChangeMap_toRingHom (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') :
    (completedBaseChangeMap I2 f).toRingHom =
      (tensorMap_adicContinuous I2 f).completionMap := rfl

/-- Finite evaluation recovers the original, same-level tensor quotient formula. -/
theorem eval_completedBaseChangeMap (I2 : Ideal A2)
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A1 B] [Algebra A1 B']
    (f : B →ₐ[A1] B') (n : ℕ) :
    (AdicCompletion.evalₐ (tensorExtensionIdeal I2 B') n).toRingHom.comp
        (completedBaseChangeMap I2 f).toRingHom =
      completedBaseChangeQuotientMap I2 f n := by
  rw [completedBaseChangeMap_toRingHom,
    RingHom.AdicContinuous.eval_completionMap]
  exact (tensorMap_adicContinuous I2 f).quotientMap_eq_of_pow_le n n
    (tensorExtensionIdeal_map_le_comap I2 f n)

/-- Completed base change preserves topological finite type under the stated ideal
containment and finite-generation hypotheses. -/
theorem completedBaseChange_topologicallyFiniteType (I2 : Ideal A2) (I1 : Ideal A1)
    {c : ℕ} (hc : 1 ≤ c) (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    {B : Type u} [CommRing B] [Algebra A1 B] (hB : TopologicallyFiniteType I1 B) :
    TopologicallyFiniteType I2 (completedBaseChange A1 I2 B) := sorry

end Algebra.TopologicallyFiniteType

namespace CommAlgCat.TopologicallyFiniteType

open Algebra.TopologicallyFiniteType

/-- The completed base-change functor between topologically finite type categories. -/
def baseChange (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG) :
    TopologicallyFiniteType.{u} A1 I1 ⥤ TopologicallyFiniteType.{u} A2 I2 where
  obj B :=
    { obj := CommAlgCat.of A2 (completedBaseChange A1 I2 B.obj)
      property := completedBaseChange_topologicallyFiniteType I2 I1 hc hI hI2 B.property }
  map f := ObjectProperty.homMk (CommAlgCat.ofHom (completedBaseChangeMap I2 f.hom.hom))
  map_id := sorry
  map_comp := sorry

/-- The object assignment of completed base change is its completed tensor carrier. -/
theorem obj_carrier (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    (B : TopologicallyFiniteType.{u} A1 I1) :
    ((baseChange I1 I2 hc hI hI2).obj B).obj =
      CommAlgCat.of A2 (completedBaseChange A1 I2 B.obj) := sorry

/-- The morphism assignment of completed base change is the completed tensor map. -/
theorem map_hom (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
    (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
    {B B' : TopologicallyFiniteType.{u} A1 I1} (f : B ⟶ B') :
    ((baseChange I1 I2 hc hI hI2).map f).hom.hom = completedBaseChangeMap I2 f.hom.hom := sorry

end CommAlgCat.TopologicallyFiniteType
