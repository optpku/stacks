/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.RefinedGysin.FlatPullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.22.6: In Situation 82.2.1 let `f : X' ⟶ X` be a flat morphism of
relative dimension `r` of good algebraic spaces over `B`. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Form the cartesian square of
Remark 82.22.3 with `i' : D' ⟶ X'` and `g : D' ⟶ D`. For any `(k + 1)`-cycle
`α` on `X` one has `(i')^* (f^* α) = g^* (i^* α)` in `CH_{k+r}(D')`, where
`f^*` is the cycle-level flat pullback, `i^*` and `(i')^*` are Gysin maps,
and `g^*` is Chow-level flat pullback. -/
@[stacks 0ER6] #check (AlgebraicGeometry.AlgebraicSpace.Hom.gysin_flatPullback_eq_flatPullback_gysin :
    ∀ {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pX = pX') (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α : cycleGroup pX δ (k + 1)),
    gysin pX' δ (k + (r : ℤ)) ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s)
        (add_right_comm k 1 (r : ℤ) ▸ flatPullbackHom pX pX' δ f r hf (k + 1) α) =
      ChowGroup.RefinedGysin.baseChangeFlatPullback pX pX' δ f r hf L s k
        (gysin pX δ k L s α))
