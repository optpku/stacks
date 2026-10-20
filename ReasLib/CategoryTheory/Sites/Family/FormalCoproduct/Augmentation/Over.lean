module

public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Equalizers
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.FiniteLimits
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Augmentation
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Presheaf.Preserves
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Products
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct

/-!
# Augmented fixed-target families as over-presheaves

An augmentation of a formal coproduct of arrows into `X` packages into a
functor to the slice of presheaves over `h_X`.  This is independent of any
Grothendieck topology and is the reusable owner for fixed-target
semi-representable-family presentations.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily
namespace OverFamily
namespace Augmentation

/-- A fixed-target semi-representable family determines a presheaf equipped with its canonical
augmentation to the representable presheaf of the target. -/
@[stacks 01G2 "fixed target, augmentation functor"]
noncomputable def toOver (X : C) :
    SemiRepresentableFamily.OverFamily.{v, u, w} X ⥤
      CategoryTheory.Over (uliftYoneda.{w}.obj X) :=
  (FormalCoproduct.forgetOver X ⋙ FormalCoproduct.toPresheaf).toOver
    (uliftYoneda.{w}.obj X)
    (fun K ↦ FormalCoproduct.augmentation K)
    (fun g ↦ FormalCoproduct.augmentation_naturality g)

/-- Forgetting the augmentation from `toOver X` recovers the formal-coproduct presheaf functor
on the underlying family. -/
@[simp, stacks 01G2 "fixed target, augmentation forgetful compatibility"]
theorem toOver_comp_forget (X : C) :
    toOver X ⋙ CategoryTheory.Over.forget (uliftYoneda.{w}.obj X) =
      FormalCoproduct.forgetOver X ⋙ FormalCoproduct.toPresheaf := sorry

/-- The source presheaf of `toOver X` is the formal-coproduct presheaf of the underlying family.
-/
@[simp, stacks 01G2 "fixed target, underlying augmented presheaf"]
theorem toOver_obj_left {X : C}
    (K : SemiRepresentableFamily.OverFamily.{v, u, w} X) :
    ((toOver X).obj K).left =
      FormalCoproduct.toPresheaf.obj ((FormalCoproduct.forgetOver X).obj K) := sorry

/-- The structure map of `toOver X` is the canonical formal-coproduct augmentation. -/
@[simp, stacks 01G2 "fixed target, canonical augmentation"]
theorem toOver_obj_hom {X : C}
    (K : SemiRepresentableFamily.OverFamily.{v, u, w} X) :
    ((toOver X).obj K).hom = FormalCoproduct.augmentation K := sorry

/-- On a family morphism, `toOver X` acts by the formal-coproduct presheaf map of the underlying
morphism. -/
@[simp, stacks 01G2 "fixed target, underlying augmentation morphism"]
theorem toOver_map_left {X : C}
    {K L : SemiRepresentableFamily.OverFamily.{v, u, w} X} (φ : K ⟶ L) :
    ((toOver X).map φ).left =
      FormalCoproduct.toPresheaf.map ((FormalCoproduct.forgetOver X).map φ) := sorry

/-- The morphism supplied by `toOver X` satisfies the canonical augmentation triangle. -/
@[reassoc, simp, stacks 01G2 "fixed target, augmentation naturality"]
theorem toOver_map_w {X : C}
    {K L : SemiRepresentableFamily.OverFamily.{v, u, w} X} (φ : K ⟶ L) :
    ((toOver X).map φ).left ≫ ((toOver X).obj L).hom = ((toOver X).obj K).hom := sorry

/-- The augmented presheaf functor of fixed-target families preserves coproducts indexed in the
formal-coproduct universe. -/
@[stacks 01G2 "fixed target, coproduct preservation"]
instance toOver.preservesCoproducts (X : C) (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (toOver X) := sorry

/-- If the ambient category has pullbacks, the augmented presheaf functor of fixed-target
families preserves finite limits. -/
@[stacks 01G2 "fixed target, finite-limit preservation"]
instance toOver.preservesFiniteLimits (X : C) [HasPullbacks C] :
    PreservesFiniteLimits (toOver X) := sorry

end Augmentation
end OverFamily
end SemiRepresentableFamily

end CategoryTheory
