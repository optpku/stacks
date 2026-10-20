module

public import ReasLib.CategoryTheory.Cofibered.PushforwardComparison

/-!
# Comparison of fibre categories along a commuting square

A cleavage of `p.op` turns a commuting square in the base into a 2-commutative square of fibre
categories. The induced functor into the 2-fibre product is `fiberComparison`.
-/

@[expose] public section

open CategoryTheory Limits CategoricalPullback Opposite
open scoped CategoricalPullback

universe u v uF vF

variable {C : Type u} [Category.{v} C]
variable {F : Type uF} [Category.{vF} F]

open CategoryTheory.Functor

variable (p : F ⥤ C) (χ : p.op.Cleavage)

section Composition

variable {U V W : C} (f : U ⟶ V) (g : V ⟶ W)

#check (CategoryTheory.Functor.pushforwardFiberCompIso p χ f g :
  pushforwardFiberFunctor p χ f ⋙ pushforwardFiberFunctor p χ g ≅
    pushforwardFiberFunctor p χ (f ≫ g))

end Composition

section Congruence

variable {U V : C} {f g : U ⟶ V} (h : f = g)

#check (CategoryTheory.Functor.pushforwardFiberCongrIso p χ h :
  pushforwardFiberFunctor p χ f ≅ pushforwardFiberFunctor p χ g)

end Congruence

section Square

variable {A A1 A2 P : C} {f1 : A1 ⟶ A} {f2 : A2 ⟶ A}
  {π1 : P ⟶ A1} {π2 : P ⟶ A2} (hw : π1 ≫ f1 = π2 ≫ f2) (y : p.Fiber P)

#check (CategoryTheory.Functor.fiberPushforwardSquare p χ hw :
  CatCommSqOver (pushforwardFiberFunctor p χ f1) (pushforwardFiberFunctor p χ f2)
    (p.Fiber P))

#check (CategoryTheory.Functor.fiberPushforwardSquare_fst p χ hw :
  (fiberPushforwardSquare p χ hw).fst = pushforwardFiberFunctor p χ π1)

#check (CategoryTheory.Functor.fiberPushforwardSquare_snd p χ hw :
  (fiberPushforwardSquare p χ hw).snd = pushforwardFiberFunctor p χ π2)

#check (CategoryTheory.Functor.fiberComparison p χ hw :
  p.Fiber P ⥤ (pushforwardFiberFunctor p χ f1) ⊡ (pushforwardFiberFunctor p χ f2))

#check (CategoryTheory.Functor.fiberComparison_obj_fst p χ hw y :
  ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y)

#check (CategoryTheory.Functor.fiberComparison_obj_snd p χ hw y :
  ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y)

#check (CategoryTheory.Functor.fiberComparison_obj_iso p χ hw y :
  ((fiberComparison p χ hw).obj y).iso = (fiberPushforwardSquare p χ hw).iso.app y)

#check (CategoryTheory.Functor.fiberComparison_spec p χ hw y :
  ((fiberComparison p χ hw).obj y).fst = (pushforwardFiberFunctor p χ π1).obj y ∧
    ((fiberComparison p χ hw).obj y).snd = (pushforwardFiberFunctor p χ π2).obj y ∧
    ((fiberComparison p χ hw).obj y).iso = (fiberPushforwardSquare p χ hw).iso.app y)

end Square
