/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.TensorSquare
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat modules along weakly etale maps

This leaf owns the tensor-square flatness criterion for flat modules.  The multiplication-map
hypothesis is kept explicit so the source-facing theorem does not silently replace it by a global
`Algebra.WeaklyEtale` instance.

@stack 092C
-/

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace Module.Flat

variable {A : Type u} {B : Type v} {N : Type w}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]

/-- Lemma 15.105.2 (092C): if the tensor-square multiplication map is flat, an `A`-flat
`B`-module is flat over `B`. -/
@[stacks 092C "tensor-square flatness criterion"]
theorem of_flat_base_and_flat_tensorSquareMultiplication
    (hflatMul : (Algebra.TensorProduct.lmul' A : B ⊗[A] B →ₐ[A] B).Flat)
    (hflatN : Module.Flat A N) :
    Module.Flat B N := sorry

/-- A flat module remains flat after changing scalars along a weakly etale algebra. -/
@[stacks 092C "weakly etale flat-module transport"]
theorem of_isWeaklyEtale [Algebra.WeaklyEtale A B]
    (hflatN : Module.Flat A N) : Module.Flat B N := sorry

end Module.Flat
