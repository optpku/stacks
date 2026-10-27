/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.ProperPushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.22.5: In Situation 82.2.1, let `f : X' ⟶ X` be a proper morphism
of good algebraic spaces over `B`. Let `(L, s, i : D ⟶ X)` be as in
Definition 82.22.1, and form the cartesian zero-scheme square of
Remark 82.22.3 with `i' : D' ⟶ X'` and `g : D' ⟶ D`. For any `(k + 1)`-cycle
`α'` on `X'`, one has `i* (f_* α') = g_* ((i')* α')` in `CH_k(D)`, where
`f_*` is the cycle-level proper pushforward, `i*` and `(i')*` are Gysin maps,
and `g_*` is Chow-level proper pushforward. -/
@[stacks 0ER5] #check (AlgebraicGeometry.AlgebraicSpace.Hom.gysin_properPushforward :
    ∀ {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) [Proper f] (hf : f ≫ pX = pX')
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α' : cycleGroup pX' δ (k + 1)),
    gysin pX δ k L s (properPushforwardHom pX' pX δ f hf (k + 1) α') =
      ChowGroup.properPushforward
        (zeroSchemeι ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) ≫ pX')
        (zeroSchemeι L s ≫ pX) δ (zeroSchemePullbackMap f L s)
        (by rw [← Category.assoc, zeroSchemePullbackMap_comp, Category.assoc, hf]) k
        (gysin pX' δ k ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) α'))
