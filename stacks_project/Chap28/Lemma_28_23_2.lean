/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap28.Definition_28_23_1
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
import StacksCheckRecall

open AlgebraicGeometry

universe u

variable (X : RingedSpace.{u}) (κ : Cardinal.{u})

/- Lemma 28.23.2: for a ringed space `X` and a cardinal `κ`, there is a set of
`κ`-generated `𝒪_X`-modules containing a representative of every isomorphism class of
`κ`-generated modules. -/
@[stacks 077M] #check
  (SheafOfModules.IsKappaGenerated.exists_set_representatives
      (R := X.ringCatSheaf) κ :
    ∃ S : Set X.Modules,
      (∀ M ∈ S, M.IsKappaGenerated κ) ∧
      ∀ M : X.Modules, M.IsKappaGenerated κ →
        ∃ N ∈ S, Nonempty (N ≅ M))
