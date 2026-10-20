/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Morita
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

/- Lemma 56.3.8 -/
@[stacks 0GP0] #check (ModuleCat.equivalence_tensor_invertible :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      (F : ModuleCat A ⥤ ModuleCat B) [F.IsEquivalence],
      ∃ (e : A ≃+* B) (L : ModuleCat B),
        Module.Invertible B L ∧
        Nonempty (F ≅
          ModuleCat.extendScalars e.toRingHom ⋙
            tensorRight L))
