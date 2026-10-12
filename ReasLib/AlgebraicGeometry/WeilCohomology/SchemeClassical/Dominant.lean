/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.SchemeClassical.Nontriviality
public import ReasLib.AlgebraicGeometry.WeilCohomology.Pushforward
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

@[expose] public section

noncomputable section

universe u v w x y z

namespace WeilCohomology

open AlgebraicGeometry CategoryTheory

namespace SchemeClassicalTheory

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type w} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ × ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}

/-- Pullback along a dominant morphism between irreducible represented schemes is injective
on total cohomology. -/
theorem pullback_injective_of_isDominant
    (T : SchemeClassicalTheory k F TateLine V dimension product fst snd point
      H CH Hgrade CHgrade cyclePullback cyclePushforward)
    {X Y : V} (f : X ⟶ Y)
    [IrreducibleSpace (T.scheme.obj X).left]
    [IrreducibleSpace (T.scheme.obj Y).left]
    [IsDominant (T.scheme.map f).left] :
    Function.Injective (T.pullback f) := sorry

end SchemeClassicalTheory

end WeilCohomology
