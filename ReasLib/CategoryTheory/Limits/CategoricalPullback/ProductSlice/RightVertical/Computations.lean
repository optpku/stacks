/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.ProductSlice.RightVertical.Basic

/-!
# Computations for the product-slice right-vertical functor

This file records the base comparison, projection, object, and morphism formulas of the
product-slice right-vertical construction.
-/

@[expose] public section

universe vC vXS uC uXS

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace Limits.CategoricalPullback.ProductSlice

section RightVertical

variable {C : Type uC} [Category.{vC} C] [Limits.HasBinaryProducts C]
variable {XS : Type uXS} [Category.{vXS} XS]
variable {U V : C} {gU : Over U ⥤ XS} {gV : Over V ⥤ XS} {xp : XS ⥤ C}

/-- The object component of `RightVertical.baseIso` is the expected composite isomorphism. -/
@[simp]
theorem RightVertical.baseIso.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    (RightVertical.baseIso eU eV).app c =
      eU.app ((Over.map Limits.prod.fst).obj c) ≪≫
        (eV.app ((Over.map Limits.prod.snd).obj c)).symm := sorry

/-- The hom component of `RightVertical.baseIso` is the expected composite. -/
@[simp]
theorem RightVertical.baseIso.hom.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    (RightVertical.baseIso eU eV).hom.app c =
      eU.hom.app ((Over.map Limits.prod.fst).obj c) ≫
        eV.inv.app ((Over.map Limits.prod.snd).obj c) := sorry
/- Proof strategy: unfold `RightVertical.baseIso` and `NatIso.ofComponents`. -/

/-- The inverse component of `RightVertical.baseIso` is the reverse composite. -/
@[simp]
theorem RightVertical.baseIso.inv.app
    (eU : gU ⋙ xp ≅ Over.forget U) (eV : gV ⋙ xp ≅ Over.forget V)
    (c : Over (Limits.prod U V)) :
    (RightVertical.baseIso eU eV).inv.app c =
      eV.hom.app ((Over.map Limits.prod.snd).obj c) ≫
        eU.inv.app ((Over.map Limits.prod.fst).obj c) := sorry

/-- The first projection of the product-slice right vertical is its `U`-leg. -/
@[simp]
theorem RightVertical.functor.fst
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp)) :
    RightVertical.functor eH ⋙ π₁ xp xp =
      Over.map Limits.prod.fst ⋙ gU := sorry

/-- The second projection of the product-slice right vertical is its `V`-leg. -/
@[simp]
theorem RightVertical.functor.snd
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp)) :
    RightVertical.functor eH ⋙ π₂ xp xp =
      Over.map Limits.prod.snd ⋙ gV := sorry

/-- The first component of a product-slice right-vertical object is obtained from the
`U`-leg. -/
@[simp]
theorem RightVertical.functor.obj.fst
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    (c : Over (Limits.prod U V)) :
    ((RightVertical.functor eH).obj c).fst =
      gU.obj ((Over.map Limits.prod.fst).obj c) := sorry

/-- The second component of a product-slice right-vertical object is obtained from the
`V`-leg. -/
@[simp]
theorem RightVertical.functor.obj.snd
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    (c : Over (Limits.prod U V)) :
    ((RightVertical.functor eH).obj c).snd =
      gV.obj ((Over.map Limits.prod.snd).obj c) := sorry

/-- The structural isomorphism of a product-slice right-vertical object is the supplied base
comparison component. -/
@[simp]
theorem RightVertical.functor.obj.iso
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    (c : Over (Limits.prod U V)) :
    ((RightVertical.functor eH).obj c).iso = eH.app c := sorry

/-- The first component of a product-slice right-vertical morphism is obtained from the
`U`-leg. -/
@[simp]
theorem RightVertical.functor.map.fst
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    ((RightVertical.functor eH).map f).fst =
      gU.map ((Over.map Limits.prod.fst).map f) := sorry

/-- The second component of a product-slice right-vertical morphism is obtained from the
`V`-leg. -/
@[simp]
theorem RightVertical.functor.map.snd
    (eH : ((Over.map (Limits.prod.fst : Limits.prod U V ⟶ U) ⋙ gU) ⋙ xp) ≅
      ((Over.map (Limits.prod.snd : Limits.prod U V ⟶ V) ⋙ gV) ⋙ xp))
    {c d : Over (Limits.prod U V)} (f : c ⟶ d) :
    ((RightVertical.functor eH).map f).snd =
      gV.map ((Over.map Limits.prod.snd).map f) := sorry

end RightVertical

end Limits.CategoricalPullback.ProductSlice

end CategoryTheory
