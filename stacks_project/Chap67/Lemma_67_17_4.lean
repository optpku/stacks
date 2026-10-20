/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.SchemeTheoreticDensity
import StacksCheckRecall

/-!
# Quasi-compact scheme-theoretic density versus closure

A quasi-compact open immersion of algebraic spaces is scheme-theoretically
dense if and only if it is scheme-theoretically dominant, i.e. the
scheme-theoretic closure of the source in the target is the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.17.4: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `ι : U ⟶ X` be an open immersion of algebraic spaces over `S`. If `ι` is
quasi-compact, then `U` is scheme-theoretically dense in `X` if and only if the
scheme-theoretic closure of `U` in `X` is `X`, equivalently if and only if `ι`
is scheme-theoretically dominant. -/
@[stacks 0835] #check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.iff_isSchemeTheoreticallyDominant :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
      [IsOpenImmersion ι] [QuasiCompact ι],
      IsSchemeTheoreticallyDense ι ↔ IsSchemeTheoreticallyDominant ι)

/- Scheme-theoretic dominance of a quasi-compact open immersion implies
scheme-theoretic density. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.of_isSchemeTheoreticallyDominant :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} {ι : U ⟶ X}
      [IsOpenImmersion ι] [QuasiCompact ι],
      IsSchemeTheoreticallyDominant ι → IsSchemeTheoreticallyDense ι)

/- A scheme-theoretically dense quasi-compact open immersion is
scheme-theoretically dominant, i.e. its scheme-theoretic closure is the
target. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.IsSchemeTheoreticallyDense.instIsSchemeTheoreticallyDominant :
    ∀ {S : Scheme.{u}} {X U : AlgebraicSpace S} (ι : U ⟶ X)
      [IsOpenImmersion ι] [QuasiCompact ι] [IsSchemeTheoreticallyDense ι],
      IsSchemeTheoreticallyDominant ι)

end AlgebraicGeometry.AlgebraicSpace
