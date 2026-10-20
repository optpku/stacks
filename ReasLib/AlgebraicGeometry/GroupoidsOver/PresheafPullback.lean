/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import ReasLib.AlgebraicGeometry.Scheme.Sites.OverPostScheme
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Restriction

/-!
# Pullback of presheaves along objects of groupoid fibrations

Selected cartesian Yoneda evaluation transports presheaves on a groupoid
fibration to the big site of the scheme underlying an object. Further
precomposition with the small étale forgetful functor gives small étale
restriction.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- Evaluation of an object `x` on schemes over `U = (X.p.obj x).left`,
sending each scheme to the selected cartesian lift of `x` in the total
category. This is the total evaluation underlying the canonical quasi-inverse
from schemes over `U` to the slice over `x`. -/
def yonedaEval (x : X.total) : Over (X.p.obj x).left ⥤ X.total :=
  Over.iteratedSliceBackward (X.p.obj x) ⋙
    toFunctor (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x)))

/-- `yonedaEval x` is iterated-slice comparison followed by the total functor of
the 2-Yoneda representative of `x`. -/
theorem yonedaEval_eq (x : X.total) :
    yonedaEval x =
      Over.iteratedSliceBackward (X.p.obj x) ⋙
        toFunctor (YonedaSlice.representative (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x))) :=
  sorry

/-- `yonedaEval` sends a scheme over `U` to the image of its iterated slice
under the 2-Yoneda representative of `x`. -/
theorem yonedaEval_obj (x : X.total) (V : Over (X.p.obj x).left) :
    (yonedaEval x).obj V =
      (toFunctor (YonedaSlice.representative
          (⟨x, rfl⟩ : X.p.Fiber (X.p.obj x)))).obj
        ((Over.iteratedSliceBackward (X.p.obj x)).obj V) :=
  sorry

/-- Pullback of an `A`-valued presheaf on the total category of `X` along an
object `x`, defined by precomposition with total Yoneda evaluation. It is the
restriction to the slice over `x`, transported to schemes over `p(x)` along
the canonical slice equivalence. -/
def pullbackPresheaf {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) : (Over (X.p.obj x).left)ᵒᵖ ⥤ A :=
  (yonedaEval x).op ⋙ F

/-- `pullbackPresheaf x F` is presheaf inverse image of `F` along `yonedaEval x`. -/
theorem pullbackPresheaf_eq {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) :
    pullbackPresheaf x F = (presheafInverseImage (yonedaEval x) A).obj F :=
  sorry

/-- Sections of the pullback over a scheme `V` over `p(x)` are the sections of
`F` on the 2-Yoneda evaluation of `V`. -/
theorem pullbackPresheaf_obj {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) (V : Over (X.p.obj x).left) :
    (pullbackPresheaf x F).obj (Opposite.op V) =
      F.obj (Opposite.op ((yonedaEval x).obj V)) :=
  sorry

/-- Precomposition of the pullback along the canonical functor from the slice
over `x` to schemes over `p(x)` recovers restriction of `F` to that slice, up
to natural isomorphism. -/
theorem pullbackPresheaf_comp_overPostScheme {A : Type a} [Category.{b} A]
    (x : X.total) (F : X.totalᵒᵖ ⥤ A) :
    Nonempty
      ((Functor.overPostScheme X.p x).op ⋙ pullbackPresheaf x F ≅
        (Over.forget x).op ⋙ F) :=
  sorry

/-- Small étale restriction is the pullback to schemes over `p(x)` precomposed
with the small étale forgetful functor. -/
theorem restrictSmallEtale_eq_pullback {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) :
    restrictSmallEtale x F =
      (Scheme.Etale.forget (X.p.obj x).left).op ⋙ pullbackPresheaf x F :=
  sorry

end AlgebraicGeometry.GroupoidsOver
