/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

variable {Z X S : Scheme.{u}}
variable (i : Z ⟶ X) [IsImmersion i] (f : X ⟶ S)

/- Lemma 29.32.15: for an immersion `i : Z ⟶ X` over `S`, the canonical sequence
`C_{Z/X} ⟶ i^* Ω_{X/S} ⟶ Ω_{Z/S} ⟶ 0` is exact. -/
@[stacks 01UZ] #check
  (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.exact_and_epi i f :
    (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.complex i f).Exact ∧
      Epi (AlgebraicGeometry.Scheme.Hom.Conormal.Differentials.comparison i f))
