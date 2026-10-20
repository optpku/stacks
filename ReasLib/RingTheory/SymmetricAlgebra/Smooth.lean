/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import ReasLib.RingTheory.Finiteness.Projective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Smooth symmetric algebras

@stack 07M6

This leaf characterizes smoothness of a symmetric algebra in terms of finite projectivity of its
module of generators.
-/

@[expose] public section

universe u v

namespace SymmetricAlgebra

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommMonoid M] [Module A M]

/-- Lemma 15.9.13 (Stacks `07M6`): the symmetric algebra on `M` is smooth over `A` exactly when
`M` is finite projective. -/
@[stacks 07M6]
theorem smooth_iff_finiteProjective :
    Algebra.Smooth A (SymmetricAlgebra A M) ↔ Module.FiniteProjective A M := sorry

end SymmetricAlgebra
