/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.StrictTransform.OpenImmersion
import StacksCheckRecall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/-! Lemma 76.39.4: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`. Let `U ⊂ B` be an open subspace. Assume `B` is
quasi-compact and quasi-separated, `U` is quasi-compact, `f : X ⟶ B` is of
finite type, and `f⁻¹(U) ⟶ U` is an isomorphism. Then there exists a
`U`-admissible blowup `B' ⟶ B` such that `U` is scheme-theoretically dense in
`B'` and such that the strict transform `X'` of `X` maps isomorphically to an
open subspace of `B'`.
-/
@[stacks 087F] #check
  (AlgebraicGeometry.AlgebraicSpace.StrictTransform.exists_admissibleBlowup :
    ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S},
      [IsQuasiCompact B] → [IsAbsolutelyQuasiSeparated B] →
      (f : X ⟶ B) → [FiniteType f] →
      (U : OpenSubspace B) → [IsQuasiCompact U.X] →
      [IsIso (pullback.snd f U.ι)] →
      ∃ (B' : AlgebraicSpace S) (b : B' ⟶ B) (Z : ClosedSubspace B)
        (h_quasiCompact :
          QuasiCompact (strictTransformOpenComplement b (Z.inverseImageSubspace b) f).ι)
        (h_open : IsOpenImmersion (pullback.snd U.ι b)),
        IsBlowup b Z ∧ FinitePresentation Z.ι ∧ Disjoint Z.pointsSet U.pointsSet ∧
          IsSchemeTheoreticallyDense (pullback.snd U.ι b) ∧
            IsOpenImmersion (strictTransformSnd b (Z.inverseImageSubspace b) f))
