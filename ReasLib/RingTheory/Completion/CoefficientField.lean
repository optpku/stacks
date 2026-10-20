/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import ReasLib.FieldTheory.Separable.Generated.Properties
public import ReasLib.RingTheory.Completion.LocalRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Coefficient Fields in Complete Local Algebras

This leaf records the equal-characteristic coefficient-field section supplied by separability of
the residue field over the chosen ground field.

@stack 0C34
-/

@[expose] public section

open IsLocalRing

universe u v

/-- Lemma 15.38.3 (Stacks `0C34`): if `A` is a complete local `k`-algebra and
`ResidueField A / k` is separable, then the residue map admits a `k`-algebra section. -/
@[stacks 0C34 "separable residue fields lift to coefficient fields"]
theorem exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver
    (A : Type v) [CommRing A] [IsCompleteLocalRing A]
    (k : Type u) [Field k] [Algebra k A]
    [Algebra.IsSeparableOver k (ResidueField A)] :
    ∃ φ : ResidueField A →ₐ[k] A,
      (residue A).comp φ = RingHom.id (ResidueField A) := sorry
