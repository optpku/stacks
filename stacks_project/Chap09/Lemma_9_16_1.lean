/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Normal.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Polynomial

universe u v

variable {F : Type u} [Field F]
variable (P : F[X])

/- Lemma 9.16.1: the canonical field `P.SplittingField` is a splitting field of `P` over `F`;
this is exactly the canonical instance `Polynomial.IsSplittingField.splittingField`. -/
@[stacks 09HU]
#check Polynomial.IsSplittingField.splittingField

variable {E : Type v} [Field E] [Algebra F E]

/- Companion check for Lemma 9.16.1: a splitting field is normal over the base field, via the
canonical theorem `Normal.of_isSplittingField`. -/
#check Normal.of_isSplittingField

/- Companion check for Lemma 9.16.1: any splitting field of `P` is `F`-algebra isomorphic to the
canonical splitting field `P.SplittingField`; this is exactly
`Polynomial.IsSplittingField.algEquiv`. -/
#check Polynomial.IsSplittingField.algEquiv
