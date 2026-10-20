/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Equivalence

@[expose] public section

universe uC vC uX vX uY vY

namespace CategoryTheory

open BasedCategory BasedFunctor Functor
open Functor.Fiber

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}
variable {U : C}

namespace BasedCategory.PseudoPullback.FstFiber

variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

/- Lemma 4.42.1 (1): the fibre over `f : V ⟶ U` of
`(C/U) ×_Y X ⟶ C/U` is equivalent to the structured-arrow category of pairs `(x, φ)` with
`x ∈ X_V` and `φ : G(f) ⟶ F(x)`. -/
@[stacks 02Y5 "(1)"]
#check (fun [Functor.IsFibered.InGroupoids pX]
    [Functor.IsFibered.InGroupoids pY] (f : Over U) ↦
  comparison.equivalence G F f :
    ∀ [Functor.IsFibered.InGroupoids pX]
        [Functor.IsFibered.InGroupoids pY] (f : Over U),
      structuredArrow G F f ≌
        ((PseudoPullback.fst G F).toFunctor).Fiber f)

/- Lemma 4.42.1 (2): the Hom-set between `(x, φ)` and `(x', φ')` is the subtype of maps
`ψ : x ⟶ x'` satisfying `φ ≫ F(ψ) = φ'`, equivalently `F(ψ) = φ⁻¹ ≫ φ'` in the groupoid
fibre. -/
@[stacks 02Y5 "(2)"]
#check (fun [Functor.IsFibered.InGroupoids pX]
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A B : structuredArrow G F f) ↦
  letI : IsIso A.hom :=
    Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom
  StructuredArrow.homEquivInv A B :
    ∀ [Functor.IsFibered.InGroupoids pX]
        [Functor.IsFibered.InGroupoids pY] (f : Over U)
        (A B : structuredArrow G F f),
      letI : IsIso A.hom :=
        Functor.IsFibered.InGroupoids.hom_isIso (p := pY) f.left A.hom
      (A ⟶ B) ≃
        {ψ : A.right ⟶ B.right //
          (F.fiberFunctor f.left).map ψ =
            (asIso A.hom).inv ≫ B.hom})

end BasedCategory.PseudoPullback.FstFiber

end CategoryTheory
