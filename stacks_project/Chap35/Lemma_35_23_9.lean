/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Dominant
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.IsDominant

/- Lemma 35.23.9: For a field extension `E/k`, a morphism of schemes over `k` is
dominant if and only if its base change to `E` is dominant. -/
@[stacks 0H8I] #check
  (AlgebraicGeometry.IsDominant.iff_fieldExtension :
    ∀ {k E : Type u} [Field k] [Field E] [Algebra k E]
      {X Y : Over (Spec (CommRingCat.of k))} (f : X ⟶ Y),
      IsDominant f.left ↔
        IsDominant (((FieldExtension.Over.functor k E).map f).left))

end AlgebraicGeometry.IsDominant
