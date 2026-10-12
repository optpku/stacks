/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_48_4_Comparison
public import stacks_project.Chap67.Lemma_67_48_4_Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.48.4 (1): if `f : X ⟶ Y` is a quasi-compact and quasi-separated morphism
of algebraic spaces over a scheme `S` and `g : W ⟶ Y` is étale, then
`W ×_Y Hom.normalization f` is the normalization of `W` in `W ×_Y X`. -/
@[stacks 0ABP] #check
  (isNormalization_pullback_snd_of_etale :
    ∀ {S : Scheme.{u}} {X Y W : AlgebraicSpace S} (f : X ⟶ Y) (g : W ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [Etale g]
      [HasPullback f g] [HasPullback (Hom.fromNormalization f) g],
      IsNormalization (pullback.snd f g) (pullbackToNormalization f g)
        (pullback.snd (Hom.fromNormalization f) g))

/- Lemma 67.48.4 (2): if `X` and `Y` are representable by schemes over `S` and
`f : X ⟶ Y` is quasi-compact and quasi-separated, then the algebraic-space
relative normalization is representable and canonically identified with the
scheme-level relative normalization of Morphisms 29.53. -/
@[stacks 0ABP] #check
  (isNormalization_ofOverMap :
    ∀ {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
      [AlgebraicGeometry.QuasiCompact f.left]
      [AlgebraicGeometry.QuasiSeparated f.left],
      IsNormalization (ofOverMap f) (ofOverToNormalization f)
        (ofOverFromNormalization f))

end AlgebraicGeometry.AlgebraicSpace
