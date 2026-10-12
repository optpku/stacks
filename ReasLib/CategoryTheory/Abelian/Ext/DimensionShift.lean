/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dimension shifting along a short exact sequence

The connecting maps of a short exact sequence become surjective when the middle term is
projective or injective, and become bijective between positive Ext degrees.  Both variance
directions are exposed symmetrically.  An actual `LinearEquiv` should only be added once its
inverse can be constructed without `sorryAx` entering non-Prop data.
@stack 0G3L
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext

noncomputable section

universe w v u t

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type t} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C]
variable {S : ShortComplex C}

/-- The contravariant connecting map associated to a short exact sequence. -/
@[stacks 0G3L "contravariant Ext boundary map"]
noncomputable abbrev contravariantBoundary
    (hS : S.ShortExact) (Y : C) (n : ℕ) :
    Ext S.X₁ Y n →ₗ[R] Ext S.X₃ Y (n + 1) :=
  hS.extClass.precompOfLinear R Y (Nat.add_comm 1 n)

/-- A projective middle term makes every contravariant connecting map surjective. -/
@[stacks 0G3L "surjective contravariant Ext boundary"]
theorem contravariantBoundary_surjective
    (hS : S.ShortExact) (Y : C) [Projective S.X₂] (n : ℕ) :
    Function.Surjective (hS.contravariantBoundary (R := R) Y n) := sorry

/-- In positive source degree, a projective middle term also makes the connecting map injective. -/
@[stacks 0G3L "injective positive contravariant Ext boundary"]
theorem contravariantBoundary_injective_succ
    (hS : S.ShortExact) (Y : C) [Projective S.X₂] (q : ℕ) :
    Function.Injective (hS.contravariantBoundary (R := R) Y (q + 1)) := sorry

/-- Dimension shifting across a short exact sequence with projective middle term is bijective. -/
@[stacks 0G3L "bijective contravariant Ext dimension shift"]
theorem contravariantBoundary_bijective_succ
    (hS : S.ShortExact) (Y : C) [Projective S.X₂] (q : ℕ) :
    Function.Bijective (hS.contravariantBoundary (R := R) Y (q + 1)) := sorry

/-- The covariant connecting map associated to a short exact sequence. -/
@[stacks 0G3L "covariant Ext boundary map"]
noncomputable abbrev covariantBoundary
    (hS : S.ShortExact) (X : C) (n : ℕ) :
    Ext X S.X₃ n →ₗ[R] Ext X S.X₁ (n + 1) :=
  hS.extClass.postcompOfLinear R X rfl

/-- An injective middle term makes every covariant connecting map surjective. -/
@[stacks 0G3L "surjective covariant Ext boundary"]
theorem covariantBoundary_surjective
    (hS : S.ShortExact) (X : C) [Injective S.X₂] (n : ℕ) :
    Function.Surjective (hS.covariantBoundary (R := R) X n) := sorry

/-- In positive source degree, an injective middle term also makes the connecting map injective. -/
@[stacks 0G3L "injective positive covariant Ext boundary"]
theorem covariantBoundary_injective_succ
    (hS : S.ShortExact) (X : C) [Injective S.X₂] (q : ℕ) :
    Function.Injective (hS.covariantBoundary (R := R) X (q + 1)) := sorry

/-- Dimension shifting across a short exact sequence with injective middle term is bijective. -/
@[stacks 0G3L "bijective covariant Ext dimension shift"]
theorem covariantBoundary_bijective_succ
    (hS : S.ShortExact) (X : C) [Injective S.X₂] (q : ℕ) :
    Function.Bijective (hS.covariantBoundary (R := R) X (q + 1)) := sorry

end CategoryTheory.ShortComplex.ShortExact
