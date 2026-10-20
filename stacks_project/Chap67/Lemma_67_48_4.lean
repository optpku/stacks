/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.SchemeComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.48.4 (1): if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic spaces over a scheme `S` and `g : W ⟶ Y` is étale, then
`W ×_Y Hom.normalization f` is the normalization of `W` in `W ×_Y X`. -/
@[stacks 0ABP] #check
  (AlgebraicGeometry.AlgebraicSpace.isNormalization_pullback_snd_of_etale :
    ∀ {S : Scheme.{u}} {X Y W : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [Etale g]
      [HasPullback f g] [HasPullback (Hom.fromNormalization f) g],
      IsNormalization (pullback.snd f g) (pullbackToNormalization f g)
        (pullback.snd (Hom.fromNormalization f) g))

/- Lemma 67.48.4 (2): for schemes over `S`, any relative-normalization
factorization is represented by and uniquely isomorphic to the scheme-level
relative normalization, compatibly with both factorization maps. -/
@[stacks 0ABP] #check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_iso_ofOverNormalization :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f.left]
      [AlgebraicGeometry.QuasiSeparated f.left]
      {N : AlgebraicSpace S} (toN : ofOver X ⟶ N) (fromN : N ⟶ ofOver Y)
      (hN : IsNormalization (ofOverMap f) toN fromN),
      ∃! e : N ≅ ofOver (ofOverNormalization f),
        toN ≫ e.hom = ofOverToNormalization f ∧
          e.hom ≫ ofOverFromNormalization f = fromN)

end AlgebraicGeometry.AlgebraicSpace
