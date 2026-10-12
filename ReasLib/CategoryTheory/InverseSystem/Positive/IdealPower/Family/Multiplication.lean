/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.IdealPower.Family
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication on a family of ideal powers

Multiplication by `a ∈ I ^ d` sends the fixed-degree tower for `n` to that for `d + n`, at the
same ambient stage.  Compatibility with the monic inclusions uniquely determines these maps, so
naturality in the ambient stage is a derived theorem rather than an extra field.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v w

namespace CategoryTheory.PNatInverseSystem.IdealPower

variable {A : Type w} [CommRing A]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear A C]

/-- Multiplication by ideal-power representatives on a two-parameter ideal-power family. -/
@[stacks 0GYL "multiplication on an ideal-power family",
  stacks 0GYN "multiplication on an ideal-power family"]
structure Family.Multiplication
    {I : Ideal A} {F : PNatInverseSystem C} (P : Family I F) where
  /-- Multiplication by `a ∈ I ^ d` at one ambient stage. -/
  stageMap : ∀ d n m : ℕ, Ideal.AssociatedGraded.stage I A d →
    ((P.fixedTower n).obj (op m) ⟶ (P.fixedTower (d + n)).obj (op m))
  /-- After inclusion into the ambient tower, the stage map is ordinary scalar multiplication. -/
  stageMap_comp_fixedι : ∀ (d n m : ℕ) (a : Ideal.AssociatedGraded.stage I A d),
    stageMap d n m a ≫ (P.fixedι (d + n)).app (op m) =
      (P.fixedι n).app (op m) ≫ ((a : A) • 𝟙 _)

/-- Family multiplication maps commute with every transition in the ambient stage. -/
theorem Family.Multiplication.stageMap_naturality
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ) {m l : ℕ} (hml : m ≤ l)
    (a : Ideal.AssociatedGraded.stage I A d) :
    (P.fixedTower n).transitionMap hml ≫ μ.stageMap d n m a =
      μ.stageMap d n l a ≫ (P.fixedTower (d + n)).transitionMap hml := sorry

/-- The stagewise multiplication maps satisfy the naturality equation in the indexing
category. -/
theorem Family.Multiplication.natTrans_naturality
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d)
    {m l : ℕᵒᵖ} (f : m ⟶ l) :
    (P.fixedTower n).map f ≫ μ.stageMap d n l.unop a =
      μ.stageMap d n m.unop a ≫ (P.fixedTower (d + n)).map f := sorry

/-- Multiplication by a fixed representative as a natural transformation between fixed-degree
towers. -/
@[stacks 0GYL "natural multiplication map between fixed ideal-power towers",
  stacks 0GYN "natural multiplication map between fixed ideal-power towers"]
def Family.Multiplication.natTrans
    {I : Ideal A} {F : PNatInverseSystem C} {P : Family I F}
    (μ : P.Multiplication) (d n : ℕ)
    (a : Ideal.AssociatedGraded.stage I A d) :
    P.fixedTower n ⟶ P.fixedTower (d + n) where
  app m := μ.stageMap d n m.unop a
  naturality _ _ f := μ.natTrans_naturality d n a f

end CategoryTheory.PNatInverseSystem.IdealPower
