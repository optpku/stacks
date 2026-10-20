/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomologySequence
import StacksCheckRecall

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : HomologicalComplex C (ComplexShape.refl PUnit.{1}))

/- Definition 12.22.3 [011X]: the homology of a differential object is the canonical homology of
its one-object homological complex. -/
@[stacks 011X]
#check (K.homology PUnit.unit : C)

/- Homology of differential objects is functorial without a source-specific notation layer. -/
#check (HomologicalComplex.homologyFunctor C (ComplexShape.refl PUnit.{1}) PUnit.unit :
  HomologicalComplex C (ComplexShape.refl PUnit.{1}) ⥤ C)

end CategoryTheory
