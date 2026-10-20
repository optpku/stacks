module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Comparison.Definition
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyLimit.Presentation.Morphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparisons Induced by Morphisms of Homotopy-Limit Presentations

This leaf turns a morphism of presentations into comparison data and composes
an existing comparison with such a morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.HomotopyLimit

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace Comparison

/-- Compatibility equation used to postcompose a comparison along a morphism of
homotopy-limit presentations. -/
theorem postcomp_comp_π {K L : SequentialInverseSystem D} {f : K ⟶ L}
    {s : Cone K} {X Y : D} {c : s.pt ⟶ X} {Q : Presentation L Y}
    (C : Comparison s c) (φ : Presentation.Hom f C.presentation Q)
    (j : ℕᵒᵖ) :
    (c ≫ φ.hom) ≫ Q.cone.π.app j =
      ((Cone.postcompose f).obj s).π.app j := sorry

/-- Postcompose a comparison along a morphism from its target presentation. -/
@[stacks 08TC]
def postcomp {K L : SequentialInverseSystem D} {f : K ⟶ L}
    {s : Cone K} {X Y : D} {c : s.pt ⟶ X} {Q : Presentation L Y}
    (C : Comparison s c) (φ : Presentation.Hom f C.presentation Q) :
    Comparison ((Cone.postcompose f).obj s) (c ≫ φ.hom) where
  presentation := Q
  comp_π := postcomp_comp_π C φ

/-- Postcomposition stores the target presentation of the presentation morphism. -/
@[simp]
theorem postcomp_presentation {K L : SequentialInverseSystem D} {f : K ⟶ L}
    {s : Cone K} {X Y : D} {c : s.pt ⟶ X} {Q : Presentation L Y}
    (C : Comparison s c) (φ : Presentation.Hom f C.presentation Q) :
    (C.postcomp φ).presentation = Q := sorry

end Comparison

namespace Presentation.Hom

/-- A morphism of homotopy-limit presentations determines comparison data from the source
presentation cone postcomposed along the tower map. -/
@[stacks 08TC]
def comparison {K L : SequentialInverseSystem D} {f : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom f P Q) :
    Comparison ((Cone.postcompose f).obj P.cone) φ.hom :=
  Comparison.ofConeHom Q φ.coneHom

/-- The target presentation stored by the comparison associated to a presentation morphism is
its target presentation. -/
@[simp]
theorem comparison_presentation {K L : SequentialInverseSystem D} {f : K ⟶ L}
    {X Y : D} {P : Presentation K X} {Q : Presentation L Y}
    (φ : Presentation.Hom f P Q) :
    φ.comparison.presentation = Q := sorry

end Presentation.Hom

end CategoryTheory.HomotopyLimit
