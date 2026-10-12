/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Sites.Presheaf.InverseImage
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap96.Lemma_96_9_1_Localizing

/-!
# Pullback of a presheaf along an object of a groupoid fibration

An object `x` of a category fibred in groupoids over `(Sch/S)_fppf` determines
the Lemma 96.9.1 equivalence `X/x ⟶ (Sch/U)_fppf` with `U = p(x)`. The
pullback `x⁻¹ F` is the restriction of a presheaf `F` to `X/x`, viewed on
`(Sch/U)_fppf` via that equivalence. The concrete representative is
precomposition with the 2-Yoneda 1-morphism of `x`, the chosen quasi-inverse.
Further precomposition with `Scheme.Etale.forget` restricts to the small étale
site of `U`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u a b

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X : GroupoidsOver S}

/-- The 2-Yoneda evaluation functor of an object `x` of `X`, sending a scheme
over `U = (X.p.obj x).left` to the selected cartesian lift of `x`. It is the
total functor of the 2-Yoneda representative of `x`, precomposed with
`Over.iteratedSliceBackward`, and is the chosen quasi-inverse of
`Functor.overPostScheme X.p x`. -/
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

/-- Pullback `x⁻¹ F` of an `A`-valued presheaf on the total category of `X`.
This is the restriction of `F` to `X/x`, viewed as a presheaf on
`(Sch/U)_fppf` with `U = p(x)` via the Lemma 96.9.1 equivalence, realized by
precomposition with the 2-Yoneda quasi-inverse `yonedaEval x`. -/
def pullbackPresheaf {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) : (Over (X.p.obj x).left)ᵒᵖ ⥤ A :=
  (yonedaEval x).op ⋙ F

/-- `pullbackPresheaf x F` is presheaf inverse image of `F` along `yonedaEval x`. -/
theorem pullbackPresheaf_eq {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) :
    pullbackPresheaf x F = (presheafInverseImage (yonedaEval x) A).obj F :=
  sorry

/-- Sections of `x⁻¹ F` over a scheme `V` over `U` are the sections of `F` on
the 2-Yoneda evaluation of `V`. -/
theorem pullbackPresheaf_obj {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) (V : Over (X.p.obj x).left) :
    (pullbackPresheaf x F).obj (Opposite.op V) =
      F.obj (Opposite.op ((yonedaEval x).obj V)) :=
  sorry

/-- Transport of `x⁻¹ F` along the Lemma 96.9.1 functor
`Functor.overPostScheme X.p x : Over x ⥤ Over U` recovers the restriction of
`F` to `X/x`. This records the source identification without choosing an
inverse as data. -/
theorem pullbackPresheaf_comp_overPostScheme {A : Type a} [Category.{b} A]
    (x : X.total) (F : X.totalᵒᵖ ⥤ A) :
    Nonempty
      ((Functor.overPostScheme X.p x).op ⋙ pullbackPresheaf x F ≅
        (Over.forget x).op ⋙ F) :=
  sorry

/-- Restriction of an `A`-valued presheaf on the total category of `X` to the
small étale site of `U = p(x)`, defined as `(x⁻¹ F)|_{U_étale}`. -/
def restrictEtalePresheaf {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) : (X.p.obj x).left.Etaleᵒᵖ ⥤ A :=
  (Scheme.Etale.forget (X.p.obj x).left).op ⋙ pullbackPresheaf x F

/-- `restrictEtalePresheaf x F` is `pullbackPresheaf x F` precomposed with
`Scheme.Etale.forget`. -/
theorem restrictEtalePresheaf_eq {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) :
    restrictEtalePresheaf x F =
      (Scheme.Etale.forget (X.p.obj x).left).op ⋙ pullbackPresheaf x F :=
  sorry

/-- Sections of `F|_{U_étale}` over an étale neighborhood `V'` are the sections
of `F` on the 2-Yoneda evaluation of the underlying scheme over `U`. -/
theorem restrictEtalePresheaf_obj {A : Type a} [Category.{b} A] (x : X.total)
    (F : X.totalᵒᵖ ⥤ A) (V' : (X.p.obj x).left.Etale) :
    (restrictEtalePresheaf x F).obj (Opposite.op V') =
      F.obj (Opposite.op ((yonedaEval x).obj
        ((Scheme.Etale.forget (X.p.obj x).left).obj V'))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
