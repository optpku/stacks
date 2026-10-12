/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.PseudoTorsor

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.9.5: the sheaf of infinitesimal parameters acts simply transitively on compatible
local deformations over every open carrying a section. -/
@[stacks 04FJ] #check
  (AlgebraicGeometry.Scheme.Hom.Deformation.act_simplyTransitive :
    ∀ {X X' Y Y' : AlgebraicGeometry.Scheme.{u}}
      (S : AlgebraicGeometry.Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
      (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
      [AlgebraicGeometry.IsFirstOrderThickening i]
      [AlgebraicGeometry.IsFirstOrderThickening j]
      [i.IsOver S] [j.IsOver S] [a.IsOver S]
      (A : (AlgebraicGeometry.Scheme.Modules.pullback a).obj
          (AlgebraicGeometry.Scheme.Hom.conormalSheaf j) ⟶
        AlgebraicGeometry.Scheme.Hom.conormalSheaf i)
      (U' : X'.Opens)
      (s : AlgebraicGeometry.Scheme.Hom.Deformation.sections S i j a A U'),
      Function.Bijective
        (fun θ : (AlgebraicGeometry.Scheme.Hom.Deformation.parameterSheaf S i a).1.obj
            (op U') ↦
          AlgebraicGeometry.Scheme.Hom.Deformation.act S i j a A U' θ s))
