/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Coproduct
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable (X : Scheme.{u})

/- Lemma 36.3.1: for a scheme `X`, the category `D_QCoh(𝒪_X)` has arbitrary
coproducts indexed by types in the fixed ambient universe. -/
@[stacks 08DT] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.hasCoproducts X :
    HasCoproducts.{u} (DerivedQCoh X))

end AlgebraicGeometry.Scheme.DerivedQCoh
