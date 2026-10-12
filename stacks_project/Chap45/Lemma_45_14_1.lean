/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.ChernCharacter
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u w x y z

/- Lemma 45.14.1: on smooth projective schemes over `k`, the data (D0), (D1),
and (D2′) satisfying (A1)–(A4), specialized to the diagonal grading
`H^(2 * i)(X)(i)`, determine a unique pullback-compatible Chern character whose
value on a line bundle `L` is `exp(c₁ᴴ(L))`. -/
@[stacks 0FIE] #check
  (WeilCohomology.SmoothProjectiveContext.existsUniqueChernCharacter :
    ∀ {k : Type u} [Field k] {V : Type w} [Category.{z} V]
      (dimension : V → ℕ) (product : V → V → V)
      (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
      (point : V) (CH : V → Type y) [∀ X, CommRing (CH X)]
      (CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)) [∀ X, GradedAlgebra (CHgrade X)]
      (cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
      (cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y)
      (pointCycle : CHgrade point 0)
      (geometry : WeilCohomology.SmoothProjectiveContext k V dimension product fst snd
        point CH CHgrade cyclePullback cyclePushforward pointCycle)
      (H : Vᵒᵖ ⥤ RingCat.{x})
      (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))
      [∀ X, GradedAlgebra (Hdiag X)]
      [∀ X, Algebra ℚ (H.obj (Opposite.op X))]
      (S : AlgebraicGeometry.ChernClass.Theory
        (geometry.scheme ⋙ Over.forget (Spec (CommRingCat.of k))) H Hdiag),
      ∃ ch : AlgebraicGeometry.ChernClass.ChernCharacter
          (geometry.scheme ⋙ Over.forget (Spec (CommRingCat.of k))) H Hdiag
          S.firstChernClass,
        ∀ ch', ch' = ch)
