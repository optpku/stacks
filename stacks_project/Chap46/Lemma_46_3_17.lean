/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

variable {A A' : CommRingCat.{u}}

/- Lemma 46.3.17: let `f : A ⟶ A'` be a ring map. If
`F : Under A ⥤ AddCommGrpCat` is adequate, then its restriction along `Under.map f`
is adequate on `A'`-algebras. The compatibility identifies the restricted tensor
functors with those obtained after extending scalars from `A` to `A'`. -/
@[stacks 06V9] #check (Adequate.precompMap :
  ∀ {A A' : CommRingCat.{u}}
    (f : A ⟶ A')
    (underline : ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}))
    (underline' : ModuleCat.{u} A' ⥤ (Under A' ⥤ AddCommGrpCat.{u}))
    (compatibility :
      underline ⋙
          (Functor.whiskeringLeft (Under A') (Under A) AddCommGrpCat.{u}).obj
            (Under.map f) ≅
        ModuleCat.extendScalars f.hom ⋙ underline')
    {F : Under A ⥤ AddCommGrpCat.{u}},
    Adequate A underline F →
      Adequate A' underline'
        ((Functor.whiskeringLeft (Under A') (Under A) AddCommGrpCat.{u}).obj
          (Under.map f) |>.obj F))
