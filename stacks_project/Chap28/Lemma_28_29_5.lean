/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.FiniteSet
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u v

/- Lemma 28.29.5: if a scheme is quasi-affine, is immersed in an affine scheme, admits an ample
invertible module, or is immersed in a projective spectrum, then every finite subset is contained
in a single affine open. -/
@[stacks 01ZY] #check (AlgebraicGeometry.Scheme.exists_affineOpen_containing_finiteSet :
  ∀ {X : Scheme.{u}}
    (hX :
      X.IsQuasiAffine ∨
        (∃ (Y : Scheme.{u}) (i : X ⟶ Y), IsAffine Y ∧ IsImmersion i) ∨
        Scheme.Modules.HasAmpleInvertibleModule X ∨
        ∃ (A : Type u) (σ : Type v) (_ : CommRing A) (_ : SetLike σ A)
          (_ : AddSubgroupClass σ A) (𝒜 : ℕ → σ) (_ : GradedRing 𝒜)
          (i : X ⟶ Proj 𝒜), IsImmersion i)
    (E : Set X) (hE : E.Finite),
    ∃ U : X.affineOpens, E ⊆ ((U : X.Opens) : Set X))
