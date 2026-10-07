module

public import ReasLib.CategoryTheory.Sites.DenseSubsite.Reflection
public import ReasLib.CategoryTheory.Sites.Precoverage.Continuous
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflection for precoverage-presented sites

This module specializes cover-dense reflection of sheaf-pushforward maps to
sites presented by stable precoverages.  The topology-level reflection result
remains owned by `Functor.IsCoverDense`.
-/

@[expose] public section

open CategoryTheory

universe uC uD vC vD w

namespace CategoryTheory.Functor.Precoverage.IsContinuous

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {J : Precoverage C} {K : Precoverage D}
variable [J.IsStableUnderBaseChange] [J.HasPullbacks]
variable [K.IsStableUnderBaseChange] [K.HasPullbacks]
variable (F : C ⥤ D)
variable [Functor.Precoverage.IsContinuous F J K]
variable [F.IsCoverDense K.toGrothendieck]

/-- Lemma 7.41.4 (1) (04D9): direct image along a cover-dense continuous
functor of precoverage-presented sites reflects monomorphisms of type-valued
sheaves. -/
@[stacks 04D9 "(1)"]
theorem reflectsMonomorphisms :
    (F.sheafPushforwardContinuous
      (Type w) J.toGrothendieck K.toGrothendieck).ReflectsMonomorphisms := sorry

/-- Lemma 7.41.4 (2) (04D9): direct image along a cover-dense continuous
functor of precoverage-presented sites reflects epimorphisms of type-valued
sheaves when the target topology admits sheafification. -/
@[stacks 04D9 "(2)"]
theorem reflectsEpimorphisms [HasSheafify J.toGrothendieck (Type w)] :
    (F.sheafPushforwardContinuous
      (Type w) J.toGrothendieck K.toGrothendieck).ReflectsEpimorphisms := sorry

#synth (F.sheafPushforwardContinuous
  (Type w) J.toGrothendieck K.toGrothendieck).ReflectsMonomorphisms

section

variable [HasSheafify J.toGrothendieck (Type w)]

#synth (F.sheafPushforwardContinuous
  (Type w) J.toGrothendieck K.toGrothendieck).ReflectsEpimorphisms

end

end CategoryTheory.Functor.Precoverage.IsContinuous
