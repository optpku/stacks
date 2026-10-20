/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Conormal

universe u

noncomputable section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

/- 31.19.1.2: the canonical morphism from the symmetric algebra of the conormal module to the
associated graded algebra. -/
@[stacks 0632] #check (idealConormalAlgebraQuotient I :
  SymmetricAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I] Ideal.AssociatedGraded.ring I)
