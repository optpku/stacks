/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 48.2.1: for a locally Noetherian scheme `X` and `K : D(𝒪_X)`, the restriction
of `K` comes from a dualizing complex on every affine open if and only if this holds on the
members of some affine open covering of `X`. -/
@[stacks 0A86] #check
  (AlgebraicGeometry.Scheme.isDualizingOnAffine_iff_exists_cover :
    ∀ {X : AlgebraicGeometry.Scheme.{u}},
      [AlgebraicGeometry.IsLocallyNoetherian X] →
      (K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) →
      (∀ U : X.affineOpens, AlgebraicGeometry.Scheme.IsDualizingOnAffine K U) ↔
        ∃ (ι : Type u) (U : ι → X.affineOpens),
          (⨆ i, (U i : X.Opens)) = ⊤ ∧
            ∀ i, AlgebraicGeometry.Scheme.IsDualizingOnAffine K (U i))
