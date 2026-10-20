module

import stacks_project.Chap28.Definition_28_23_1
import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
import StacksCheckRecall

open AlgebraicGeometry

universe u

variable (X : RingedSpace.{u}) (κ : Cardinal.{u})

/- Lemma 28.23.2: for a ringed space `X` and a cardinal `κ`, there is a set `T` (a type in
the universe of `X`) and a family `(F t)_{t ∈ T}` of `κ`-generated `𝒪_X`-modules such that
every `κ`-generated module is isomorphic to one of the `F t`. -/
@[stacks 077M] #check
  (SheafOfModules.IsKappaGenerated.exists_set_representatives
      (R := X.ringCatSheaf) κ :
    ∃ (T : Type u) (F : T → X.Modules),
      (∀ t, (F t).IsKappaGenerated κ) ∧
      ∀ M : X.Modules, M.IsKappaGenerated κ →
        ∃ t, Nonempty (F t ≅ M))
