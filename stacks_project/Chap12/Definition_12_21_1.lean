/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.ExactCouple
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Definition 12.21.1 (tag `011Q`): an exact couple consists of two objects and three maps forming
an exact triangle. Morphisms are pairs commuting with all three structure maps. -/
@[stacks 011Q]
#check (ExactCouple C)

#check (ExactCouple.Hom : ExactCouple C → ExactCouple C → Type _)
#check (inferInstance : Category (ExactCouple C))
#check (ExactCouple.d : (X : ExactCouple C) → X.E ⟶ X.E)
#check (ExactCouple.d_comp_d : (X : ExactCouple C) → X.d ≫ X.d = 0)
#check (ExactCouple.pageOf :
  (X : ExactCouple C) → (d_squared : X.d ≫ X.d = 0) →
    HomologicalComplex C (ComplexShape.refl PUnit.{1}))
#check (ExactCouple.pageShortComplexOf :
  (X : ExactCouple C) → (d_squared : X.d ≫ X.d = 0) → ShortComplex C)
#check @ExactCouple.Hom.pageMapOf
#check (ExactCouple.page :
  (X : ExactCouple C) → HomologicalComplex C (ComplexShape.refl PUnit.{1}))
#check (ExactCouple.pageShortComplex : (X : ExactCouple C) → ShortComplex C)
#check @ExactCouple.Hom.pageMap
#check (ExactCouple.pageFunctor C :
  ExactCouple C ⥤ HomologicalComplex C (ComplexShape.refl PUnit.{1}))

end CategoryTheory
