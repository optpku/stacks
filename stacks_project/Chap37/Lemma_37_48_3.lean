/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Extension
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

/- Lemma 37.48.3: a surjective integral morphism over an open subscheme extends to a
surjective integral morphism over the ambient scheme whose pullback is isomorphic to the
original morphism over the open subscheme. -/
@[stacks 0CNX]
#check (AlgebraicGeometry.IsIntegralHom.exists_surjective_extension :
  ∀ {S V : Scheme.{u}} (U : S.Opens) (p : V ⟶ U) [Surjective p] [IsIntegralHom p],
    ∃ (Vbar : Scheme.{u}) (q : Vbar ⟶ S),
      IsIntegralHom q ∧ Surjective q ∧
        Nonempty (Over.mk (pullback.snd q U.ι) ≅ Over.mk p))
