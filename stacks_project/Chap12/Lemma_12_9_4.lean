/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.FiniteLength
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/- Lemma 12.9.4: in a short exact sequence the middle object is Artinian iff the two outer
objects are Artinian. -/
@[stacks 0FCH]
#check ShortComplex.isArtinianObject_iff_of_shortExact (S := S)

/- The reusable owner is the Serre-class structure on Artinian objects. -/
#check (inferInstance : (isArtinianObject : ObjectProperty C).IsSerreClass)

end CategoryTheory
