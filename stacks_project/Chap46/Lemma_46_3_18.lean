module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {A A' : CommRingCat.{u}}

/- Lemma 46.3.18: let `f : A ⟶ A'` be a ring map. If `F'` is adequate as a
module-valued functor on `A'`-algebras, then the functor
`B ↦ F'((Under.pushout f).obj B)`, equivalently `B ↦ F'(A' ⊗[A] B)`, is adequate
on `A`-algebras. The compatibility is the canonical identification of tensor functors
after restricting an `A'`-module to an `A`-module. -/
@[stacks 06VA] #check (Adequate.precompPushout :
  ∀ {A A' : CommRingCat.{u}}
    (f : A ⟶ A')
    (underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (underline' : ModuleCat.{u} A' ⥤ (Under A' ⥤ AddCommGrpCat.{u}))
    (compatibility :
      underline' ⋙
          (Functor.whiskeringLeft (Under A) (Under A') AddCommGrpCat.{u}).obj
            (Under.pushout f) ≅
        ModuleCat.restrictScalars f.hom ⋙ underline)
    {F' : Under A' ⥤ AddCommGrpCat.{u}},
    Adequate A' underline' F' →
      Adequate A underline
        ((Functor.whiskeringLeft (Under A) (Under A') AddCommGrpCat.{u}).obj
          (Under.pushout f) |>.obj F'))
