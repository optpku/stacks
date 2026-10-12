/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan.StructureMap
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pushout.AdmissibleSpan
import StacksCheckRecall

/-!
# Lemma 81.7.1

A scheme-theoretic pushout of an admissible span of schemes over `S` remains a
pushout in algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open Scheme.Pushout Scheme.Pushout.IsAdmissibleSpan

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 81.7.1: In Situation 37.67.1, let `Y ⨿_Z X` be the pushout in the category of
schemes (Proposition 37.67.3). Then the same square is a pushout in `AlgebraicSpace S`. -/
@[stacks 0EDP] #check
  (AlgebraicGeometry.AlgebraicSpace.isPushout_ofOver_admissibleSpan :
    ∀ {S : Scheme.{u}} {Z X Y P : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y) (inl : X ⟶ P) (inr : Y ⟶ P),
      [IsAdmissibleSpan i j] →
      IsPushout i.left j.left inl.left inr.left →
      IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map j)
        ((schemeFunctor S).map inl) ((schemeFunctor S).map inr))

#check
  (AlgebraicGeometry.AlgebraicSpace.isPushout_ofOver_admissibleSpan_toBase :
    ∀ {S : Scheme.{u}} {Z X Y : Over S}
      (i : Z ⟶ X) (j : Z ⟶ Y),
      [IsAdmissibleSpan i j] →
      IsPushout ((schemeFunctor S).map i) ((schemeFunctor S).map j)
        ((schemeFunctor S).map (Over.homMk (pushout.inl i.left j.left) (inl_toBase i j) :
          X ⟶ Over.mk (toBase i j)))
        ((schemeFunctor S).map (Over.homMk (pushout.inr i.left j.left) (inr_toBase i j) :
          Y ⟶ Over.mk (toBase i j))))

end AlgebraicGeometry.AlgebraicSpace
