/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap37.Lemma_37_9_5

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry

universe u

/- The multiplicative compatibility presentation of the deformation action is the explicit
pseudo-torsor on its deformation sheaf. -/
#check
  (AlgebraicGeometry.Scheme.Hom.Deformation.pseudoTorsor :
    ∀ {X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
      (S : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
      (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [AlgebraicGeometry.IsFirstOrderThickening i]
      [AlgebraicGeometry.IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S]
      (A : (AlgebraicGeometry.Scheme.Modules.pullback a).obj
          (AlgebraicGeometry.Scheme.Hom.conormalSheaf j) ⟶
        AlgebraicGeometry.Scheme.Hom.conormalSheaf i),
      CategoryTheory.Sheaf.PseudoTorsor
        (CategoryTheory.Sheaf.toSheafOfGroups
          (AlgebraicGeometry.Scheme.Hom.Deformation.parameterSheaf S i a)))
