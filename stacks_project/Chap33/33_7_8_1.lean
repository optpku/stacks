/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Galois.Basic

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped AlgebraicGeometry

universe u

variable (k : Type u) [Field k]
variable (X : Scheme.{u})
variable (f : X ⟶ Spec (CommRingCat.of k))

/- 33.7.8.1 (Tag 038A): for a scheme `X` over a field `k`, the geometric base change
`X ×[Spec k] Spec (AlgebraicClosure k)` carries the canonical action of
`Gal(AlgebraicClosure k / k)ᵐᵒᵖ` by automorphisms.  This is the algebraic-closure specialization
of the neutral field-extension Galois action. -/
@[stacks 038A] #check
  (AlgebraicGeometry.FieldExtension.Galois.opAutHom k (AlgebraicClosure k) f :
    (Gal(AlgebraicClosure k/k))ᵐᵒᵖ →*
      CategoryTheory.Aut
        (AlgebraicGeometry.FieldExtension.baseChange k (AlgebraicClosure k) f))
