/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Coh

/-! # The open locus of invertibility in a coherent family -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- For a flat, finitely presented, proper morphism, each coherent family admits
an open subscheme of its test scheme through which exactly the base changes
with tensor-invertible pulled-back module factor. -/
theorem exists_opens_isInvertible_iff (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] (x : CohStack.Obj f) :
    ∃ U : (x.σ.left.left).Opens,
      ∀ {τ : CohStack.SchemesOver B} (h : τ ⟶ x.σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
          isInvertibleObject
            ((Modules.pullback (CohStack.fiberMap f h)).obj x.module) := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
