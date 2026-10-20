/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extending Nonnegative Cochain Complexes

This file packages extension by zero from `ℕ`-indexed cochain complexes as a functor to
bounded-below `ℤ`-indexed cochain complexes.  The underlying functor remains
`ComplexShape.embeddingUpNat.extendFunctor`; the boundedness proof is kept behind a separate
proposition-valued theorem.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v u

namespace CochainComplex.Plus

variable (C : Type u) [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Extension by zero of a nonnegative cochain complex is bounded below, with lower bound zero. -/
@[stacks 01GY "extension of a nonnegative complex is bounded below"]
theorem extendNat_obj_mem (K : CochainComplex C ℕ) :
    CochainComplex.plus C ((embeddingUpNat.extendFunctor C).obj K) := sorry

/-- The canonical functor extending an `ℕ`-indexed cochain complex by zero and regarding it as
a bounded-below `ℤ`-indexed cochain complex. -/
@[stacks 01GY "extension of nonnegative complexes to bounded-below complexes"]
noncomputable def extendNat :
    CochainComplex C ℕ ⥤ CochainComplex.Plus C :=
  (CochainComplex.plus C).lift
    (embeddingUpNat.extendFunctor C) (extendNat_obj_mem C)

/-- Forgetting the bounded-below structure after `extendNat` recovers extension by zero. -/
@[stacks 01GY "underlying functor of nonnegative extension"]
noncomputable def extendNatCompInclusionIso :
    extendNat C ⋙ CochainComplex.Plus.ι C ≅ embeddingUpNat.extendFunctor C :=
  ObjectProperty.liftCompιIso
    (CochainComplex.plus C) (embeddingUpNat.extendFunctor C) (extendNat_obj_mem C)

/-- The underlying object of `extendNat` is the extension by zero of the original complex. -/
@[simp, stacks 01GY "object computation for nonnegative extension"]
theorem extendNat_obj (K : CochainComplex C ℕ) :
    ((extendNat C).obj K).obj = K.extend embeddingUpNat := sorry

/-- The underlying morphism of `extendNat` is the extension by zero of the original morphism. -/
@[simp, stacks 01GY "morphism computation for nonnegative extension"]
theorem extendNat_map {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    ((extendNat C).map f).hom = HomologicalComplex.extendMap f embeddingUpNat := sorry

end CochainComplex.Plus


