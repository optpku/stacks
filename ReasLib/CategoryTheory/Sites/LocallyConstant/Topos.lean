module

public import ReasLib.CategoryTheory.Sites.GlobalSections.ToposMorphism
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally constant sheaves and inverse image

The inverse image of a morphism of topoi preserves set-valued locally constant sheaves.  The
predicate-refined statement is the reusable owner: it remembers restrictions such as finiteness
on the constant models, while the ordinary locally constant statement is its source-facing
specialization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory.MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
variable [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
variable [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]

/-- Lemma 18.43.2, predicate-refined form: inverse image along a morphism of topoi preserves
set-valued locally constant sheaves without changing the allowed constant models. -/
@[stacks 093R "predicate"]
theorem inverseImage_isLocallyConstantWith (f : MorphismOfTopoiIn JD JC)
    (P : Type w → Prop) (F : Sheaf JD (Type w))
    [Sheaf.IsLocallyConstantWith (J := JD) P F] :
    Sheaf.IsLocallyConstantWith (J := JC) P ((f⁻¹).obj F) := sorry

/-- Lemma 18.43.2: inverse image along a morphism of topoi preserves set-valued locally constant
sheaves. -/
@[stacks 093R]
theorem inverseImage_isLocallyConstant (f : MorphismOfTopoiIn JD JC)
    (F : Sheaf JD (Type w)) [Sheaf.IsLocallyConstant F] :
    Sheaf.IsLocallyConstant ((f⁻¹).obj F) := sorry

end CategoryTheory.MorphismOfTopoiIn
