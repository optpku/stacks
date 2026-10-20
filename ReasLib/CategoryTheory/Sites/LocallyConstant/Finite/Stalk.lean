module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.CategoryTheory.Sites.Point.Basic

@[expose] public section

universe u v w

namespace CategoryTheory.Sheaf.IsFiniteLocallyConstant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
variable {F : Sheaf J (Type w)}

/-- The fiber of a finite locally constant sheaf of sets at any supplied site point
is finite. -/
theorem finite_sheafFiber (hF : IsFiniteLocallyConstant F)
    (point : GrothendieckTopology.Point.{w} J) :
    Finite (point.sheafFiber.obj F) := sorry

/-- Fibers of finite locally constant sheaves at supplied site points carry
canonical finiteness instances. -/
instance instFiniteSheafFiber [hF : IsFiniteLocallyConstant F]
    (point : GrothendieckTopology.Point.{w} J) :
    Finite (point.sheafFiber.obj F) :=
  finite_sheafFiber hF point

end CategoryTheory.Sheaf.IsFiniteLocallyConstant
