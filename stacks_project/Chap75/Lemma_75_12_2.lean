/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.ArtinianPushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/- Lemma 75.12.2. Let `S` be an affine scheme. Let `X` be a Noetherian algebraic
space over `S`. Every injective object of `QCoh X` is a direct summand of a small
filtered colimit of quasi-coherent sheaves of the form `(Z_i ⟶ X)_* G_i`, where
each `Z_i` is the spectrum of an Artinian ring and each `G_i` is a coherent
module on `Z_i`. -/
@[stacks 09TJ] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.injective_retractClosure_ind_artinianSpecCoherentPushforward :
    ∀ {S : Scheme.{u}} [IsAffine S] {X : AlgebraicSpace S} [IsNoetherian X]
      (J : QCoh X) [Injective J],
      (isArtinianSpecCoherentPushforward X).ind.{u}.retractClosure J)

end AlgebraicGeometry.AlgebraicSpace.QCoh
