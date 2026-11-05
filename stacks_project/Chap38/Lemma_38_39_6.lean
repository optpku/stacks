/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.FlatProperDescent
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 38.39.6: A finite locally free module on the source of a flat proper
morphism to a normal Noetherian scheme, free after every stalk base change of
codimension at most one, is the pullback of a finite locally free module on the base.
The dimension-zero requirement repairs an omission in the source statement of Tag 0EXG;
its canonical evaluation argument needs the generic points as well as height-one points. -/
@[stacks 0EXG] #check
  (AlgebraicGeometry.Scheme.Hom.FlatDescent.existsFiniteLocallyFreePullback :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [IsProper f] [IsNoetherian S]
      (hSnormal : S.isNormal)
      [IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
      (E : X.Modules) [E.IsFiniteLocallyFree]
      (hfree : ∀ s : S, ringKrullDim (S.presheaf.stalk s) ≤ 1 →
        ((Scheme.Modules.pullback (pullback.fst f (S.fromSpecStalk s))).obj E).IsFree),
      ∃ (F : S.Modules) (_ : F.IsFiniteLocallyFree),
        Nonempty (E ≅ (Scheme.Modules.pullback f).obj F))
