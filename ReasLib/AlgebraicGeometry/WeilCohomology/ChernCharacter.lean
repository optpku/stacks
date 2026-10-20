/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.WeilCohomology.SmoothProjective

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w x y z

namespace WeilCohomology.SmoothProjectiveContext

/-- A Chern-class theory on the diagonal cohomology of smooth projective varieties
determines a unique pullback-natural Chern character with the prescribed first Chern class. -/
theorem existsUniqueChernCharacter
    {k : Type u} [Field k] {V : Type w} [Category.{z} V]
    (dimension : V → ℕ) (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (point : V) (CH : V → Type y) [∀ X, CommRing (CH X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)) [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
    (pointCycle : CHgrade point 0)
    (geometry : SmoothProjectiveContext k V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle)
    (H : Vᵒᵖ ⥤ RingCat.{x})
    (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
    [∀ X, GradedAlgebra (Hdiag X)]
    [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
    (S : AlgebraicGeometry.ChernClass.CohomologyTheory
      (geometry.scheme ⋙ Over.forget (Spec (CommRingCat.of k))) H Hdiag) :
    ∃ ch : AlgebraicGeometry.ChernClass.ChernCharacter
        (geometry.scheme ⋙ Over.forget (Spec (CommRingCat.of k))) H Hdiag
        S.firstChernClass,
      ∀ ch', ch' = ch := sorry

end WeilCohomology.SmoothProjectiveContext
