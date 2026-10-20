/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Lean.Parser.Command
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.CommSq
import StacksCheckRecall

@[expose] public section

/-!
# 10.131.4.1

@stack 00RQ
-/

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

variable {R S R' S' : CommRingCat.{u}}
variable (α : R ⟶ S) (β : R' ⟶ S') (ψ : R ⟶ R') (φ : S ⟶ S')

/- Domain triage:
* primary domain: categorical commutative squares in `CommRingCat`;
* sampled owner API: `CategoryTheory.CommSq`, `NatTrans.commSq`, `IsPullback.toCommSq`, and the
  downstream ring-theoretic bridge `CommRingCat.KaehlerDifferential.map`;
* source-facing layer: the displayed commutative square of commutative rings;
* core/canonical owner: `CategoryTheory.CommSq`;
* bridge/view: constructions built from a commutative ring square, such as the induced map on
  Kähler differentials in `10_131_4_2`.

The primitive data are only the four ring maps. The square itself is already canonically owned by
`CommSq`, so this file should stay a direct owner recall rather than introducing any ring-specific
wrapper or local duplicate.
-/

/- 10.131.4.1: The ring maps `α : R → S`, `β : R' → S'`, `ψ : R → R'`, and
`φ : S → S'` form a commutative square of commutative rings. This is exactly the canonical
`CommRingCat` specialization of `CategoryTheory.CommSq`. -/
@[stacks 00RQ]
#check
  CommSq ψ α β φ
