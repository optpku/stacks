/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.HomotopyCategory.Trace
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Pretriangulated DerivedCategory
open scoped CategoryTheory

/- Lemma 110.64.1: there exists a ring `R`, a distinguished triangle `T` in its
homotopy category, and an endomorphism `φ : T ⟶ T` such that all three vertices
are perfect and the traces of the endomorphism are not additive. -/
@[stacks 087L] #check
  (HomotopyCategory.exists_distinguishedTriangle_traceNatural_not_additive :
    ∃ (R : Type u) (_ : Ring R)
      (T : Triangle (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ))) (φ : T ⟶ T)
      (h₁ : IsPerfect (Qh.obj T.obj₁)) (h₂ : IsPerfect (Qh.obj T.obj₂))
      (h₃ : IsPerfect (Qh.obj T.obj₃)),
      T ∈ distTriang (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) ∧
        h₁.traceNatural (Qh.map φ.hom₁) + h₃.traceNatural (Qh.map φ.hom₃) ≠
          h₂.traceNatural (Qh.map φ.hom₂))
