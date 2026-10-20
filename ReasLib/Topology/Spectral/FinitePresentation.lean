/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Spectral.FiniteLimit

/-!
# Finite Inverse-System Presentations of Spectral Spaces

This module gives the source-facing finite `T₀` inverse-system presentation as
an equivalence on the canonical `SpectralSpace` predicate.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace SpectralSpace

/-- Lemma 5.23.14: a topological space is spectral exactly when it is
homeomorphic to the limit of a directed inverse system of finite `T₀` spaces. -/
@[stacks 09XX]
theorem iff_homeomorphic_directedLimit_finiteT0
    (X : Type u) [TopologicalSpace X] :
    SpectralSpace X ↔
      ∃ (J : Type u) (_ : Preorder J) (_ : Nonempty J) (_ : IsDirectedOrder J)
        (F : Jᵒᵖ ⥤ TopCat.{u}) (_ : ∀ j : Jᵒᵖ, Finite (F.obj j))
        (_ : ∀ j : Jᵒᵖ, T0Space (F.obj j)),
        Nonempty (X ≃ₜ (limit F : TopCat)) := sorry

end SpectralSpace
