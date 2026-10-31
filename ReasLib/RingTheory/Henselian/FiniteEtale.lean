/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Etale.Finite
public import Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

/-!
# Finite etale reduction over henselian pairs

Mathlib owns `CommAlgCat.FiniteEtale` and its general base-change functor.
This leaf adds the henselian-pair fact that base change to `A ⧸ I` is an
equivalence.  Neither the category nor the reduction construction requires a
local-ring hypothesis.

@stack 09ZL
@stack 04GK
-/

universe u v

namespace CommAlgCat.FiniteEtale

variable {A : Type u} [CommRing A]

/-- Reduction modulo `I` on finite etale `A`-algebras, implemented by the
canonical Mathlib base-change functor along `A → A ⧸ I`.  The carrier
universe is chosen uniformly on both sides, so the equivalence instance
also applies to downstream categories living above the base-ring universe. -/
@[stacks 09ZL "finite-etale quotient reduction view"]
abbrev reduction (I : Ideal A) :
    CommAlgCat.FiniteEtale.{max u v} A ⥤ CommAlgCat.FiniteEtale.{max u v} (A ⧸ I) :=
  CommAlgCat.FiniteEtale.baseChange A (A ⧸ I)

/-- Lemma 15.13.2: reduction modulo an ideal in a henselian pair is the canonical equivalence on
finite etale algebras. Lemma 10.153.7 is its henselian-local-ring specialization. -/
@[stacks 09ZL "finite-etale reduction over a henselian pair"]
instance reduction_isEquivalence (I : Ideal A) [HenselianRing A I] :
    Functor.IsEquivalence (reduction.{u, v} I) := sorry

end CommAlgCat.FiniteEtale
