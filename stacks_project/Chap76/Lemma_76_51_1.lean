/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Definition_75_20_2_TorIndependence

/-!
# Tor independence after flat base change of a commutative square of algebraic spaces

For a commutative square of algebraic spaces over a scheme `S`, if `Y' ⟶ B'` and
`Z' ⟶ X'` are flat, then after base change along `B ⟶ B'` the fibre product
`X ×_B Y` and `Z'` are Tor independent over `X' ×_{B'} Y'`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.TorIndependentOver

/-- The comparison morphism `X ×_B Y ⟶ X' ×_{B'} Y'` induced by the base changes of
`X'` and `Y'` along `B ⟶ B'`. -/
def baseChangeProductHom {S : Scheme.{u}} {X' Y' B' B : AlgebraicSpace S}
    (p : X' ⟶ B') (q : Y' ⟶ B') (s : B ⟶ B') :
    pullback (pullback.snd p s) (pullback.snd q s) ⟶ pullback p q :=
  pullback.map (pullback.snd p s) (pullback.snd q s) p q
    (pullback.fst p s) (pullback.fst q s) s
    pullback.condition.symm pullback.condition.symm

/-- The first projection of `baseChangeProductHom` is the base change of `X'` along
`B ⟶ B'`. -/
theorem baseChangeProductHom_fst {S : Scheme.{u}} {X' Y' B' B : AlgebraicSpace S}
    (p : X' ⟶ B') (q : Y' ⟶ B') (s : B ⟶ B') :
    baseChangeProductHom p q s ≫ pullback.fst p q =
      pullback.fst (pullback.snd p s) (pullback.snd q s) ≫ pullback.fst p s :=
  sorry

/-- The second projection of `baseChangeProductHom` is the base change of `Y'` along
`B ⟶ B'`. -/
theorem baseChangeProductHom_snd {S : Scheme.{u}} {X' Y' B' B : AlgebraicSpace S}
    (p : X' ⟶ B') (q : Y' ⟶ B') (s : B ⟶ B') :
    baseChangeProductHom p q s ≫ pullback.snd p q =
      pullback.snd (pullback.snd p s) (pullback.snd q s) ≫ pullback.fst q s :=
  sorry

/-- The mediating morphism `Z' ⟶ X' ×_{B'} Y'` induced by a commutative square. -/
def liftOfCommSq {S : Scheme.{u}} {Z' Y' X' B' : AlgebraicSpace S}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (sq : CommSq i g q p) :
    Z' ⟶ pullback p q :=
  pullback.lift g i sq.w.symm

/-- The mediating morphism `liftOfCommSq` recovers `Z' ⟶ X'`. -/
theorem liftOfCommSq_fst {S : Scheme.{u}} {Z' Y' X' B' : AlgebraicSpace S}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (sq : CommSq i g q p) :
    liftOfCommSq i g q p sq ≫ pullback.fst p q = g :=
  sorry

/-- The mediating morphism `liftOfCommSq` recovers `Z' ⟶ Y'`. -/
theorem liftOfCommSq_snd {S : Scheme.{u}} {Z' Y' X' B' : AlgebraicSpace S}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (sq : CommSq i g q p) :
    liftOfCommSq i g q p sq ≫ pullback.snd p q = i :=
  sorry

/-- Lemma 76.51.1: for a commutative square of algebraic spaces over a scheme `S`,
if `Y' ⟶ B'` and `Z' ⟶ X'` are flat, then after base change along `B ⟶ B'` the
fibre product `X ×_B Y` and `Z'` are Tor independent over `X' ×_{B'} Y'`. -/
@[stacks 0CTQ]
theorem baseChangeProduct_of_flat {S : Scheme.{u}} {Z' Y' X' B' B : AlgebraicSpace S}
    (i : Z' ⟶ Y') (g : Z' ⟶ X') (q : Y' ⟶ B') (p : X' ⟶ B') (s : B ⟶ B')
    [Flat q] [Flat g] (sq : CommSq i g q p) :
    AlgebraicSpace.TorIndependentOver
      (Over.mk (baseChangeProductHom p q s)) (Over.mk (liftOfCommSq i g q p sq)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
