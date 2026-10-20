/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap82.Definition_82_22_1_Gysin
public import stacks_project.Chap82.Lemma_82_22_6_Pullback
public import stacks_project.Chap82.Remark_82_22_3_Pullback

/-!
# Gysin maps commute with proper pushforward

In Situation 82.2.1, the refined Gysin homomorphism of a section of an
invertible module commutes with proper pushforward, taking the first
pushforward on cycles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The canonical map from the zero scheme of a pulled-back section is proper
whenever the original morphism is proper. -/
instance instProper_zeroSchemePullbackMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [Proper f] (L : X.Modules)
    [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)] :
    Proper (zeroSchemePullbackMap f L s) :=
  sorry

/-- Lemma 82.22.5: In Situation 82.2.1, let `f : X' ⟶ X` be a proper morphism
of good algebraic spaces over `B`. Let `(L, s, i : D ⟶ X)` be as in
Definition 82.22.1, and form the cartesian zero-scheme square of
Remark 82.22.3 with `i' : D' ⟶ X'` and `g : D' ⟶ D`. For any `(k + 1)`-cycle
`α'` on `X'`, one has `i* (f_* α') = g_* ((i')* α')` in `CH_k(D)`, where
`f_*` is the cycle-level proper pushforward, `i*` and `(i')*` are Gysin maps,
and `g_*` is Chow-level proper pushforward. -/
@[stacks 0ER5]
theorem gysin_properPushforward {S : Scheme.{u}}
    {B X X' : AlgebraicSpace S} [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pX' : X' ⟶ B) [QuasiSeparated pX'] [LocallyOfFiniteType pX']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X' ⟶ X) [Proper f] (hf : f ≫ pX = pX')
    (L : X.Modules) [isInvertibleObject L] (s : L.sections)
    [isInvertibleObject ((Modules.pullback f).obj L)]
    (k : ℤ) (α' : cycleGroup pX' δ (k + 1)) :
    gysin pX δ k L s
        (properPushforwardHom δ pX' pX f hf (k + 1) α') =
      properPushforward δ
        (zeroSchemeι ((Modules.pullback f).obj L)
            (Modules.sectionsPullback f L s) ≫ pX')
        (zeroSchemeι L s ≫ pX) (zeroSchemePullbackMap f L s)
        (zeroSchemePullbackMap_comp_structure pX pX' f hf L s) k
        (gysin pX' δ k ((Modules.pullback f).obj L)
          (Modules.sectionsPullback f L s) α') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
