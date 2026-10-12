/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.Adams.Total
public import ReasLib.AlgebraicGeometry.ChernClass.Adams.ChernCharacter
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v w x

/- Lemma 45.12.5 (1): the second Adams operation multiplies the degree-`i`
coefficient of a total Chern class by `2 ^ i`. -/
@[stacks 0FIA] #check
  (AlgebraicGeometry.ChernClass.TotalChernClass.coeff_adamsTwo :
    {C : Type u} → [Category.{v} C] → (toScheme : C ⥤ Scheme.{w}) →
    (A : Cᵒᵖ ⥤ RingCat.{x}) →
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))) →
    [∀ X, GradedAlgebra (Agrade X)] → (S : AlgebraicGeometry.ChernClass.Theory toScheme A Agrade) →
    (c : AlgebraicGeometry.ChernClass.TotalChernClass
      toScheme A Agrade S.firstChernClass) →
    (X : C) → (α : Scheme.VectorBundleK0 (toScheme.obj X)) → (i : ℕ) →
    PowerSeries.coeff i
        (c.app X (Scheme.VectorBundleK0.adamsTwo (toScheme.obj X) α)) =
      (2 ^ i : ℕ) • PowerSeries.coeff i (c.app X α))

/- Lemma 45.12.5 (2): the second Adams operation multiplies the degree-`i`
coefficient of a Chern character by `2 ^ i`. -/
@[stacks 0FIA] #check
  (AlgebraicGeometry.ChernClass.ChernCharacter.coeff_adamsTwo :
    {C : Type u} → [Category.{v} C] → (toScheme : C ⥤ Scheme.{w}) →
    (A : Cᵒᵖ ⥤ RingCat.{x}) →
    (Agrade : ∀ X, ℕ → Submodule ℤ (A.obj (Opposite.op X))) →
    [∀ X, GradedAlgebra (Agrade X)] → [∀ X, Algebra ℚ (A.obj (Opposite.op X))] →
    (S : AlgebraicGeometry.ChernClass.Theory toScheme A Agrade) →
    (ch : AlgebraicGeometry.ChernClass.ChernCharacter
      toScheme A Agrade S.firstChernClass) →
    (X : C) → (α : Scheme.VectorBundleK0 (toScheme.obj X)) → (i : ℕ) →
    PowerSeries.coeff i
        (ch.app X (Scheme.VectorBundleK0.adamsTwo (toScheme.obj X) α)) =
      (2 ^ i : ℕ) • PowerSeries.coeff i (ch.app X α))
