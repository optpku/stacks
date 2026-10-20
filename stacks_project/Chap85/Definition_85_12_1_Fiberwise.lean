/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

/-!
# Stage restriction and simplex-operator inverse image on a fiberwise site

Case B of Situation 85.3.3: restriction along `ι` and inverse image `f_φ⁻¹` along
`toposMap`. The inverse-image mate `F(φ) : f_φ⁻¹ F_m ⟶ F_n` is not assembled here;
cartesianness for this item is the Case A owner in `Definition_85_12_1_Cartesian`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [h_fiberwise : HasSheafTransitions F J]
include h_fiberwise
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]

/-- Fiber inclusion `ι F (op n)` is continuous for the fiberwise total topology. -/
instance ι_isContinuous (n : SimplexCategory) :
    (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J) :=
  h_fiberwise.component_continuous n

/-- Fiber inclusion `ι F (op n)` is cocontinuous for the fiberwise total topology. -/
instance ι_isCocontinuous (n : SimplexCategory) :
    (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J) :=
  h_fiberwise.component_cocontinuous n

/-- Restriction of a sheaf on the Grothendieck total site to the degree-`n` fiber. -/
def component (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory) :
    Sheaf (topology F J) A ⥤ Sheaf ((J (op n)).toGrothendieck) A :=
  (ι F (op n)).sheafPushforwardContinuous A (J (op n)).toGrothendieck (topology F J)

/-- `component n` is continuous sheaf pushforward along `ι F (op n)`. -/
theorem component_eq (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory) :
    component F J A n =
      (ι F (op n)).sheafPushforwardContinuous A (J (op n)).toGrothendieck (topology F J) :=
  sorry

/-- Inverse image `f_φ⁻¹` of type-valued sheaves along a simplex operator, as cocontinuous
sheaf pullback. -/
def inverseImage {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P] :
    Sheaf ((J (op m)).toGrothendieck) (Type w) ⥤
      Sheaf ((J (op n)).toGrothendieck) (Type w) :=
  (F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
    (J (op n)).toGrothendieck (J (op m)).toGrothendieck

/-- `inverseImage φ` is cocontinuous sheaf pullback along `u_φ`. -/
theorem inverseImage_eq {m n : SimplexCategory} (φ : m ⟶ n)
    [∀ (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
      ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P] :
    inverseImage F J φ =
      (F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (J (op m)).toGrothendieck :=
  sorry

/-- Restriction along the total-category arrows `ιNatTrans` gives a map of
presheaves from the precomposition of the stage-`m` sheaf to the stage-`n` sheaf.
Its source need not be a sheaf; inverse-image comparison requires sheafification. -/
def transitionDirect {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (topology F J) (Type w)) :
    (F.map φ.op).toFunctor.op ⋙ ((component F J (Type w) m).obj G).obj ⟶
      ((component F J (Type w) n).obj G).obj :=
  whiskerRight (NatTrans.op (ιNatTrans φ.op)) G.obj

/-- The presheaf transition is whiskering of the opposite total-category
comparison with the underlying presheaf. -/
theorem transitionDirect_eq {m n : SimplexCategory} (φ : m ⟶ n)
    (G : Sheaf (topology F J) (Type w)) :
    transitionDirect F J φ G =
      whiskerRight (NatTrans.op (ιNatTrans φ.op)) G.obj :=
  rfl

end CategoryTheory.Grothendieck
