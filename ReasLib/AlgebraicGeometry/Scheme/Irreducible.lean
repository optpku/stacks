/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits

/-!
# Irreducible schemes

Affine-open recognition principles for irreducible schemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is irreducible exactly when it admits a nonempty affine open cover by
irreducible members whose pairwise intersections are nonempty. -/
theorem irreducibleSpace_iff_exists_affineOpenCover :
    IrreducibleSpace X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        Nonempty 𝒰.I₀ ∧
          (∀ i : 𝒰.I₀, IsIrreducible ((𝒰.f i).opensRange : Set X)) ∧
            ∀ i j : 𝒰.I₀,
              (((𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange : X.Opens) : Set X).Nonempty := sorry

/-- A scheme is irreducible exactly when it is nonempty and every nonempty affine open
subset is irreducible. -/
theorem irreducibleSpace_iff_nonempty_and_forall_nonempty_affineOpen :
    IrreducibleSpace X ↔
      Nonempty X ∧
        ∀ U : X.affineOpens,
          ((U : Set X).Nonempty → IsIrreducible (U : Set X)) := sorry

end AlgebraicGeometry.Scheme
