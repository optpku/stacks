/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap81.Lemma_81_6_3_Gluing
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Pushout.Gluing
open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 81.6.3 (1): base change along the canonical thickening–affine pushout gives a
functor from algebraic spaces over the pushout to compatible pairs over `Y` and `X'`. -/
@[stacks 07VY] #check
  (baseChange :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      Over (pushout i f) ⥤ CategoricalPullback (Over.pullback f) (Over.pullback i))

/- Lemma 81.6.3 (2): base change sends schemes over the pushout to schemes over `Y`. -/
@[stacks 07VY] #check
  (baseChange_fst_isScheme :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (Z : Over (pushout i f)) [IsScheme Z.left],
      IsScheme ((baseChange i f).obj Z).fst.left)

/- Lemma 81.6.3 (3): base change sends schemes over the pushout to schemes over `X'`. -/
@[stacks 07VY] #check
  (baseChange_snd_isScheme :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f] (Z : Over (pushout i f)) [IsScheme Z.left],
      IsScheme ((baseChange i f).obj Z).snd.left)

/- Lemma 81.6.3 (4): a compatible pair is sent to the overlap pushout
`V ⨿_{(V ×_Y X)} U'` in algebraic spaces over the canonical pushout. -/
@[stacks 07VY] #check
  (glue :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f],
      CategoricalPullback (Over.pullback f) (Over.pullback i) ⥤ Over (pushout i f))

/- Lemma 81.6.3 (5): pushout gluing is left adjoint to base change. -/
@[stacks 07VY] #check
  (adjunction :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f], glue i f ⊣ baseChange i f)

/- Lemma 81.6.3 (6): pushout gluing of a compatible pair of schemes is a scheme. -/
@[stacks 07VY] #check
  (glue_isScheme :
    ∀ {S : Scheme.{u}} {X X' Y : AlgebraicSpace S} (i : X ⟶ X') (f : X ⟶ Y)
      [IsThickening i] [Affine f]
      (P : CategoricalPullback (Over.pullback f) (Over.pullback i))
      [IsScheme P.fst.left] [IsScheme P.snd.left],
      IsScheme ((glue i f).obj P).left)
