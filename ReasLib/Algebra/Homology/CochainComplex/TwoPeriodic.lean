/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-Periodic Endomorphism Complexes

This file bundles a pair of square-zero endomorphisms and realizes it as a `ZMod 2`-indexed
cochain complex.  The bundle keeps the two differentials and their compatibility laws available
without threading four parallel arguments through every consumer.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory

/-- A two-periodic differential on one object: two endomorphisms whose composites in both
orders vanish. -/
@[stacks 02MW]
structure TwoPeriodicEndomorphism (C : Type u) [Category.{v} C] [HasZeroMorphisms C] where
  /-- The object in both degrees. -/
  X : C
  /-- The differential from degree `0` to degree `1`. -/
  d₀ : X ⟶ X
  /-- The differential from degree `1` to degree `0`. -/
  d₁ : X ⟶ X
  /-- The degree-`0` differential followed by the degree-`1` differential vanishes. -/
  d₀_d₁ : d₀ ≫ d₁ = 0
  /-- The degree-`1` differential followed by the degree-`0` differential vanishes. -/
  d₁_d₀ : d₁ ≫ d₀ = 0

namespace TwoPeriodicEndomorphism

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The alternating differential of a two-periodic endomorphism satisfies the cochain-complex
square-zero relation at every degree. -/
theorem differential_comp_differential (K : TwoPeriodicEndomorphism C) (i : ZMod 2) :
    (if i = 0 then K.d₀ else K.d₁) ≫
      (if i + 1 = 0 then K.d₀ else K.d₁) = 0 := sorry

/-- The `ZMod 2`-indexed cochain complex associated to a two-periodic endomorphism. -/
@[stacks 02MW]
def toCochainComplex (K : TwoPeriodicEndomorphism C) : CochainComplex C (ZMod 2) :=
  CochainComplex.of
    (fun _ ↦ K.X)
    (fun i ↦ if i = 0 then K.d₀ else K.d₁)
    K.differential_comp_differential

/-- Every term of the associated cochain complex is the underlying object. -/
@[simp]
theorem toCochainComplex_X (K : TwoPeriodicEndomorphism C) (i : ZMod 2) :
    K.toCochainComplex.X i = K.X := sorry

/-- The differential from degree `0` to degree `1` is `d₀`. -/
@[simp]
theorem toCochainComplex_d_zero (K : TwoPeriodicEndomorphism C) :
    K.toCochainComplex.d 0 1 = K.d₀ := sorry

/-- The differential from degree `1` to degree `0` is `d₁`. -/
@[simp]
theorem toCochainComplex_d_one (K : TwoPeriodicEndomorphism C) :
    K.toCochainComplex.d 1 0 = K.d₁ := sorry

end TwoPeriodicEndomorphism

end CategoryTheory
