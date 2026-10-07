module

public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived
public import ReasLib.CategoryTheory.Pro.Sequential.DerivedLimit.Milnor
public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement

/-!
# First derived inverse-limit maps from sequential representatives

The Milnor product square of a sequential representative descends to the neutral canonical
cokernel model `SequentialInverseSystem.Milnor.ProductCone.canonicalR1`.  The resulting map
respects identities and composition and depends only on the represented pro-morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory.Pro.SequentialHom

open SequentialInverseSystem.Milnor.ProductCone

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {X Y : SequentialInverseSystem C}
variable [HasCountableProducts C] [HasCokernels C]

/-- The representative-level map on the canonical first derived inverse limits. -/
noncomputable def firstDerivedLimitMap (r : Pro.SequentialHom X Y) :
    canonicalR1 X ⟶ canonicalR1 Y :=
  cokernel.map X.milnorDifferenceMap Y.milnorDifferenceMap
    r.firstProductMap r.secondProductMap (r.milnorDifferenceCommSq).w

/-- The cokernel-projection specification of `firstDerivedLimitMap`. -/
theorem cokernel_π_comp_firstDerivedLimitMap (r : Pro.SequentialHom X Y) :
    canonicalR1.π X ≫ r.firstDerivedLimitMap =
      r.secondProductMap ≫ canonicalR1.π Y := sorry

/-- Identity representatives induce identity maps on the neutral canonical Milnor cokernel. -/
@[simp]
theorem firstDerivedLimitMap_id (X : SequentialInverseSystem C) :
    (Pro.SequentialHom.id X).firstDerivedLimitMap = 𝟙 (canonicalR1 X) := sorry

/-- Composition of representatives composes their maps on canonical Milnor cokernels. -/
@[simp]
theorem firstDerivedLimitMap_comp {Z : SequentialInverseSystem C}
    (r : Pro.SequentialHom X Y) (s : Pro.SequentialHom Y Z) :
    (Pro.SequentialHom.comp r s).firstDerivedLimitMap =
      r.firstDerivedLimitMap ≫ s.firstDerivedLimitMap := sorry

/-- Equivalent sequential representatives induce the same map on canonical Milnor cokernels. -/
theorem firstDerivedLimitMap_eq_of_toHom_eq
    {r s : Pro.SequentialHom X Y} (h : r.toHom = s.toHom) :
    r.firstDerivedLimitMap = s.firstDerivedLimitMap := sorry

/-- Common-refinement equivalent representatives induce the same map on canonical Milnor
cokernels. -/
theorem firstDerivedLimitMap_eq_of_equivalent
    {r s : Pro.SequentialHom X Y} (h : Equivalent r s) :
    r.firstDerivedLimitMap = s.firstDerivedLimitMap := sorry

end CategoryTheory.Pro.SequentialHom
