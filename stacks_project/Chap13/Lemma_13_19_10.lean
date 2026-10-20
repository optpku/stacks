/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Vanishing
import ReasLib.Algebra.Homology.DerivedCategory.KProjective.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ComplexShape

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {P : ProjectiveMinus A} {K : CochainComplex A ℤ} (n : ℤ)
variable (hP : (P : CochainComplex A ℤ).IsStrictlyGE n)
variable (hK : ∀ i : ℤ, n ≤ i → IsZero (K.homology i))

/- Lemma 13.19.10 is the bounded-above termwise-projective specialization of the K-projective
vanishing API.  Its homotopy-category and derived-category conclusions are exposed separately. -/
@[stacks 064D "homotopy-category vanishing"]
#check (IsKProjective.Vanishing.homotopy n hP hK :
  ∀ f : (HomotopyCategory.quotient A (up ℤ)).obj P ⟶
    (HomotopyCategory.quotient A (up ℤ)).obj K, f = 0)

section

variable [HasDerivedCategory.{w} A]

@[stacks 064D "derived-category vanishing"]
#check (IsKProjective.Vanishing.derived n hP hK :
  ∀ f : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj K, f = 0)

end

end CochainComplex
