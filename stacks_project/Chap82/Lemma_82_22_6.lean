/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Lemma_82_22_6_Pullback

/-!
# Gysin maps commute with flat pullback

In Situation 82.2.1, the refined Gysin homomorphism of a section of an
invertible module commutes with flat pullback of relative dimension `r`,
taking the first pullback on cycles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 82.22.6: In Situation 82.2.1 let `f : X' ⟶ X` be a flat morphism of
relative dimension `r` of good algebraic spaces over `B`. Let
`(L, s, i : D ⟶ X)` be as in Definition 82.22.1. Form the cartesian square of
Remark 82.22.3 with `i' : D' ⟶ X'` and `g : D' ⟶ D`. For any `(k + 1)`-cycle
`α` on `X` one has `(i')^* (f^* α) = g^* (i^* α)` in `CH_{k+r}(D')`, where
`f^*` is the cycle-level flat pullback, `i^*` and `(i')^*` are Gysin maps,
and `g^*` is Chow-level flat pullback. -/
@[stacks 0ER6]
theorem gysin_flatPullback_eq_flatPullback_gysin {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pX = pX') (L : X.Modules) [isInvertibleObject L]
    (s : L.sections) [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α : cycleGroup pX δ (k + 1)) :
    gysin pX' δ (k + (r : ℤ)) ((Modules.pullback f).obj L)
        (Modules.sectionsPullback f L s)
        (add_right_comm k 1 (r : ℤ) ▸
          flatPullbackHom δ pX pX' f r hf (k + 1) α) =
      chowFlatPullback δ (zeroSchemeι L s ≫ pX)
        (zeroSchemeι ((Modules.pullback f).obj L)
            (Modules.sectionsPullback f L s) ≫ pX')
        (zeroSchemePullbackMap f L s) r
        (zeroSchemePullbackMap_comp_structure pX pX' f hf L s) k
        (gysin pX δ k L s α) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
