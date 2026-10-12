/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.KFlat

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

/- Lemma 36.3.6: if `K` is a K-flat complex of modules over a commutative ring `R`,
then the degreewise associated complex `K̃` of `𝒪_(Spec R)`-modules is K-flat. -/
@[stacks 08DV] #check
  (CochainComplex.IsKFlat.tilde :
    {R : CommRingCat.{u}} → {K : CochainComplex (ModuleCat R) ℤ} → K.IsKFlat →
      (((AlgebraicGeometry.tilde.functor R).mapHomologicalComplex (up ℤ)).obj K).IsKFlat)
