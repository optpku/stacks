/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Limit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Milnor Rows for Sequential Inverse Systems

@stack 0H31

This leaf owns the product, inverse-limit, difference, and canonical first-derived-limit rows
attached to a short complex of sequential inverse systems of abelian groups. It also provides the
three explicit morphisms between those rows and their zero-composite laws.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe v

namespace CategoryTheory.ShortComplex.ShortExact

open SequentialInverseSystem.Milnor SequentialInverseSystem.Milnor.ProductCone

/-- The product maps induced by a short complex still compose to zero. -/
theorem productRow_zero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    SequentialInverseSystem.productMap S.f ≫
      SequentialInverseSystem.productMap S.g = 0 := by
  apply Pi.hom_ext
  intro n
  simpa only [SequentialInverseSystem.productMap, Category.assoc, Pi.lift_π,
    Pi.lift_π_assoc, NatTrans.comp_app, NatTrans.app_zero, comp_zero, zero_comp] using
    congrArg (fun φ : S.X₁ ⟶ S.X₃ ↦ Pi.π S.X₁.family n ≫ φ.app (Opposite.op n)) S.zero

/-- The product row induced by a short complex of sequential inverse systems of abelian groups.
Its maps are the canonical maps on Milnor products. -/
@[stacks 0H31 "Milnor product row"]
noncomputable def productRow
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk
    (SequentialInverseSystem.productMap S.f)
    (SequentialInverseSystem.productMap S.g)
    (productRow_zero S)

/-- The left square formed by the limit-to-product maps commutes. -/
theorem limitToProductHom_comm₁₂
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    limitToProduct S.X₁ ≫ (productRow S).f =
      (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).f ≫
        limitToProduct S.X₂ := by
  change limitToProduct S.X₁ ≫ SequentialInverseSystem.productMap S.f =
    limMap S.f ≫ limitToProduct S.X₂
  apply Pi.hom_ext
  intro n
  simp only [limitToProduct, SequentialInverseSystem.productMap, Category.assoc,
    Pi.lift_π, Pi.lift_π_assoc, limMap_π]

/-- The right square formed by the limit-to-product maps commutes. -/
theorem limitToProductHom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    limitToProduct S.X₂ ≫ (productRow S).g =
      (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).g ≫
        limitToProduct S.X₃ := by
  change limitToProduct S.X₂ ≫ SequentialInverseSystem.productMap S.g =
    limMap S.g ≫ limitToProduct S.X₃
  apply Pi.hom_ext
  intro n
  simp only [limitToProduct, SequentialInverseSystem.productMap, Category.assoc,
    Pi.lift_π, Pi.lift_π_assoc, limMap_π]

/-- The morphism from the limit row to the corresponding product row. -/
noncomputable def limitToProductHom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v}) ⟶
      productRow S where
  τ₁ := limitToProduct S.X₁
  τ₂ := limitToProduct S.X₂
  τ₃ := limitToProduct S.X₃
  comm₁₂ := limitToProductHom_comm₁₂ S
  comm₂₃ := limitToProductHom_comm₂₃ S

private theorem difference_productMap_comm
    {K L : SequentialInverseSystem AddCommGrpCat.{v}} (f : K ⟶ L) :
    K.milnorDifferenceMap ≫ SequentialInverseSystem.productMap f =
      SequentialInverseSystem.productMap f ≫ L.milnorDifferenceMap := by
  apply Pi.hom_ext
  intro n
  simp only [SequentialInverseSystem.milnorDifferenceMap,
    SequentialInverseSystem.productMap, Preadditive.sub_comp, Preadditive.comp_sub,
    Category.id_comp, Category.comp_id, Category.assoc, Pi.lift_π, Pi.lift_π_assoc,
    Pi.map'_comp_π, Pi.map'_comp_π_assoc]
  rw [f.naturality (homOfLE (Nat.le_succ n)).op]

/-- Milnor difference maps commute with the left product-row map. -/
theorem milnorDifferenceHom_comm₁₂
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    S.X₁.milnorDifferenceMap ≫ (productRow S).f =
      (productRow S).f ≫ S.X₂.milnorDifferenceMap := by
  exact difference_productMap_comm S.f

/-- Milnor difference maps commute with the right product-row map. -/
theorem milnorDifferenceHom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    S.X₂.milnorDifferenceMap ≫ (productRow S).g =
      (productRow S).g ≫ S.X₃.milnorDifferenceMap := by
  exact difference_productMap_comm S.g

/-- The morphism between the two product rows whose components are Milnor difference maps. -/
noncomputable def milnorDifferenceHom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    productRow S ⟶ productRow S where
  τ₁ := S.X₁.milnorDifferenceMap
  τ₂ := S.X₂.milnorDifferenceMap
  τ₃ := S.X₃.milnorDifferenceMap
  comm₁₂ := milnorDifferenceHom_comm₁₂ S
  comm₂₃ := milnorDifferenceHom_comm₂₃ S

/-- The maps induced on canonical Milnor cokernels by a short complex compose to zero. -/
theorem r1Row_zero
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    canonicalR1.map S.f ≫ canonicalR1.map S.g = 0 := by
  apply (cancel_epi (canonicalR1.π S.X₁)).1
  simp only [canonicalR1.π, canonicalR1.map, cokernel.map, cokernel.π_desc_assoc,
    cokernel.π_desc, Category.assoc, comp_zero]
  rw [← Category.assoc, productRow_zero S, zero_comp]

/-- The row formed by the canonical Milnor cokernels of the three systems. -/
noncomputable def r1Row
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (canonicalR1.map S.f) (canonicalR1.map S.g) (r1Row_zero S)

/-- Canonical Milnor quotients commute with the left map from the product row. -/
theorem productToR1Hom_comm₁₂
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    canonicalR1.π S.X₁ ≫ (r1Row S).f =
      (productRow S).f ≫ canonicalR1.π S.X₂ := by
  exact cokernel.π_desc _ _ _

/-- Canonical Milnor quotients commute with the right map from the product row. -/
theorem productToR1Hom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    canonicalR1.π S.X₂ ≫ (r1Row S).g =
      (productRow S).g ≫ canonicalR1.π S.X₃ := by
  exact cokernel.π_desc _ _ _

/-- The quotient morphism from the Milnor product row to the canonical Milnor-cokernel row. -/
noncomputable def productToR1Hom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    productRow S ⟶ r1Row S where
  τ₁ := canonicalR1.π S.X₁
  τ₂ := canonicalR1.π S.X₂
  τ₃ := canonicalR1.π S.X₃
  comm₁₂ := productToR1Hom_comm₁₂ S
  comm₂₃ := productToR1Hom_comm₂₃ S

/-- The limit-to-product morphism followed by the Milnor difference morphism is zero. -/
theorem limitToProductHom_comp_milnorDifferenceHom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    limitToProductHom S ≫ milnorDifferenceHom S = 0 := by
  have h (K : SequentialInverseSystem AddCommGrpCat.{v}) :
      limitToProduct K ≫ K.milnorDifferenceMap = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [limitToProduct, SequentialInverseSystem.milnorDifferenceMap,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Category.assoc, Pi.lift_π, Pi.lift_π_assoc, Pi.map'_comp_π,
      zero_comp]
    exact sub_eq_zero.mpr (limit.w K (homOfLE (Nat.le_succ n)).op).symm
  apply ShortComplex.hom_ext
  · exact h S.X₁
  · exact h S.X₂
  · exact h S.X₃

/-- The Milnor difference morphism followed by the quotient to the `R1` row is zero. -/
theorem milnorDifferenceHom_comp_productToR1Hom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    milnorDifferenceHom S ≫ productToR1Hom S = 0 := by
  apply ShortComplex.hom_ext
  · exact cokernel.condition S.X₁.milnorDifferenceMap
  · exact cokernel.condition S.X₂.milnorDifferenceMap
  · exact cokernel.condition S.X₃.milnorDifferenceMap

end CategoryTheory.ShortComplex.ShortExact
