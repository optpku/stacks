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
      SequentialInverseSystem.productMap S.g = 0 := sorry

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
        limitToProduct S.X₂ := sorry

/-- The right square formed by the limit-to-product maps commutes. -/
theorem limitToProductHom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    limitToProduct S.X₂ ≫ (productRow S).g =
      (S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})).g ≫
        limitToProduct S.X₃ := sorry

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

/-- Milnor difference maps commute with the left product-row map. -/
theorem milnorDifferenceHom_comm₁₂
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    S.X₁.milnorDifferenceMap ≫ (productRow S).f =
      (productRow S).f ≫ S.X₂.milnorDifferenceMap := sorry

/-- Milnor difference maps commute with the right product-row map. -/
theorem milnorDifferenceHom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    S.X₂.milnorDifferenceMap ≫ (productRow S).g =
      (productRow S).g ≫ S.X₃.milnorDifferenceMap := sorry

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
    canonicalR1.map S.f ≫ canonicalR1.map S.g = 0 := sorry

/-- The row formed by the canonical Milnor cokernels of the three systems. -/
noncomputable def r1Row
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    ShortComplex AddCommGrpCat.{v} :=
  ShortComplex.mk (canonicalR1.map S.f) (canonicalR1.map S.g) (r1Row_zero S)

/-- Canonical Milnor quotients commute with the left map from the product row. -/
theorem productToR1Hom_comm₁₂
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    canonicalR1.π S.X₁ ≫ (r1Row S).f =
      (productRow S).f ≫ canonicalR1.π S.X₂ := sorry

/-- Canonical Milnor quotients commute with the right map from the product row. -/
theorem productToR1Hom_comm₂₃
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    canonicalR1.π S.X₂ ≫ (r1Row S).g =
      (productRow S).g ≫ canonicalR1.π S.X₃ := sorry

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
    limitToProductHom S ≫ milnorDifferenceHom S = 0 := sorry

/-- The Milnor difference morphism followed by the quotient to the `R1` row is zero. -/
theorem milnorDifferenceHom_comp_productToR1Hom
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) :
    milnorDifferenceHom S ≫ productToR1Hom S = 0 := sorry

end CategoryTheory.ShortComplex.ShortExact
