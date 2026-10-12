/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_28_10_Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

/- Lemma 67.28.10 (1): if `f : X ⟶ Y` is locally of finite type, then its
diagonal `pullback.diagonal f : X ⟶ X ×[Y] X` is locally of finite
presentation. -/
@[stacks 084P] #check
  (LocallyOfFinitePresentation.diagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f],
      LocallyOfFinitePresentation (pullback.diagonal f))

/- Lemma 67.28.10 (2): if `f : X ⟶ Y` is quasi-separated and locally of finite
type, then its diagonal `pullback.diagonal f : X ⟶ X ×[Y] X` is of finite
presentation. -/
@[stacks 084P] #check
  (FinitePresentation.diagonal :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiSeparated f] [LocallyOfFiniteType f],
      FinitePresentation (pullback.diagonal f))
