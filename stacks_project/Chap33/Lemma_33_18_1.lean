/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.NoetherNormalization

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 33.18.1: let `f : X ⟶ S` be a morphism of schemes, let `x : X`, and let `V` be an
affine open neighborhood of `f x`. If `f` is locally of finite type and
`f.fiberDimensionAt x = (d : WithBot ℕ∞)`, then there exists an affine open neighborhood `U` of
`x` inside `f ⁻¹ᵁ V` and a factorization of the restriction `U.toScheme ⟶ V.toScheme` through
relative affine `d`-space over `V.toScheme` such that the map to affine space is quasi-finite. -/
@[stacks 0CBH] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_quasiFinite_to_affineSpace_of_fiberDimensionAt :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (x : X) (d : ℕ) (hfdim : f.fiberDimensionAt x = (d : WithBot ℕ∞))
      (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)),
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
          let A := AffineSpace (ULift.{u} (Fin d)) ((V : S.Opens).toScheme)
          ∃ π : ((U : X.Opens).toScheme) ⟶ A,
            Scheme.Hom.QuasiFinite π ∧
              π ≫ (A ↘ ((V : S.Opens).toScheme)) = f.resLE (V : S.Opens) (U : X.Opens) e)
