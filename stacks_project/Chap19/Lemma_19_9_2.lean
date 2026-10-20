/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Exact.Abelian.SheafYoneda
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

noncomputable section

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A]

/- Lemma 19.9.2 (05PN) (1): additive representables are sheaves for the singleton-epimorphism
topology. -/
@[stacks 05PN "representables are sheaves"] #check
  (Abelian.preadditiveYoneda_isSheaf A :
    ∀ X : A, Presheaf.IsSheaf (Abelian.epiTopology A) (preadditiveYoneda.obj X))

/- Lemma 19.9.2 (05PN) (2): the resulting sheaf-valued Yoneda functor is fully faithful. -/
@[stacks 05PN "full"] #check
  (inferInstance : Functor.Full (Abelian.sheafYoneda A))

@[stacks 05PN "faithful"] #check
  (inferInstance : Functor.Faithful (Abelian.sheafYoneda A))

/- Lemma 19.9.2 (05PN) (3): the sheaf-valued Yoneda functor is exact. -/
@[stacks 05PN "exact"] #check
  (Abelian.sheafYonedaExact A :
    A ⥤ₑ Sheaf (Abelian.epiTopology A) AddCommGrpCat.{v})

/- Lemma 19.9.2 (05PN) (4): the singleton-epimorphism site has enough points. -/
@[stacks 05PN "enough points"] #check
  (inferInstance : GrothendieckTopology.HasEnoughPoints.{max (u + 1) (v + 1)}
    (Abelian.epiTopology A))

end CategoryTheory
