/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.BeckChevalley

/-!
# Base change on slice sites

A commutative square in a site induces a Beck-Chevalley transformation between the associated
direct-image and inverse-image functors on sheaves.  For a cartesian square this transformation
is invertible.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.GrothendieckTopology.Over.BaseChange

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {X' X Y' Y : C}
variable (i : X' ⟶ X) (p : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [Functor.IsCocontinuous (Over.map f) (J.over X) (J.over Y)]
variable [Functor.IsCocontinuous (Over.map p) (J.over X') (J.over Y')]
variable [Functor.IsContinuous (Over.map g) (J.over Y') (J.over Y)]
variable [Functor.IsContinuous (Over.map i) (J.over X') (J.over X)]
variable [∀ F : (CategoryTheory.Over X')ᵒᵖ ⥤ Type w,
  (Over.map p).op.HasPointwiseRightKanExtension F]
variable [∀ F : (CategoryTheory.Over X)ᵒᵖ ⥤ Type w,
  (Over.map f).op.HasPointwiseRightKanExtension F]
variable [HasWeakSheafify (J.over X') (Type w)]
variable [HasWeakSheafify (J.over X) (Type w)]

/-- The Beck-Chevalley transformation on sheaves induced by a commutative square of slice
categories. -/
noncomputable def map (hcomm : i ≫ f = p ≫ g) :
    (Over.map f).sheafPushforwardCocontinuous (Type w) (J.over X) (J.over Y) ⋙
        (Over.map g).sheafPushforwardContinuous (Type w) (J.over Y') (J.over Y) ⟶
      (Over.map i).sheafPushforwardContinuous (Type w) (J.over X') (J.over X) ⋙
        (Over.map p).sheafPushforwardCocontinuous (Type w) (J.over X') (J.over Y') :=
  CatCommSq.BeckChevalley.comparison
    (J.over X') (J.over X) (J.over Y') (J.over Y)
    (CategoryTheory.Over.mapCommSq i p f g hcomm)

/-- The Beck-Chevalley transformation of a cartesian square of slice sites is invertible. -/
noncomputable instance map_isIso
    [Functor.IsCocontinuous (Over.map g) (J.over Y') (J.over Y)]
    [Functor.IsCocontinuous (Over.map i) (J.over X') (J.over X)]
    (hcart : IsPullback i p f g) :
    IsIso (map J i p f g hcart.w) := sorry

end CategoryTheory.GrothendieckTopology.Over.BaseChange

