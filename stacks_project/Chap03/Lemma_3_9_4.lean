/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Size
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry
open scoped Cardinal AlgebraicGeometry

/- Lemma 3.9.4: the size of an affine scheme is the maximum of the countable
cardinal and the cardinality of its global section ring. -/
@[stacks 000P] #check (AlgebraicGeometry.Scheme.size_of_isAffine :
  ∀ (S : Scheme.{u}) [IsAffine S], S.size = #(Γ(S, ⊤)) ⊔ ℵ₀)

#check (AlgebraicGeometry.Scheme.size_Spec :
  ∀ (R : CommRingCat.{u}), (Spec R).size = #R ⊔ ℵ₀)
