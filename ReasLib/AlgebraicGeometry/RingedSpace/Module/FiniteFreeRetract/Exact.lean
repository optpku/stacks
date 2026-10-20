module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local splittings of exact sequences on ringed spaces

Finite locally free module sheaves are locally finite-free retracts, so an exact sequence whose
last term is finite locally free splits after restriction to a suitable cover.  This file is the
opens-site specialization of the generic ringed-site existence API; it does not choose a cover or
splitting.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract

variable {X : RingedSpace.{u}}

/-- A short exact complex ending in a finite locally free module sheaf splits on a cover after
restriction to any open subset. -/
@[stacks 0B38 "local splitting over an open subset"]
theorem existsCover_splittingOver
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₃.IsFiniteLocallyFree] (U : Opens X) :
    ∃ (I : Type u) (Ui : I → Over U),
      ((Opens.grothendieckTopology X).over U).CoversTop Ui ∧
        ∀ i : I,
          Nonempty
            (((S.map (SheafOfModules.Localization.restriction X.ringCatSheaf U)).map
              (SheafOfModules.Localization.restriction
                (X.ringCatSheaf.over U) (Ui i))).Splitting) := sorry

/-- A short exact complex ending in a finite locally free module sheaf splits after restriction
to every member of a cover of the ringed space. -/
@[stacks 0B38 "splitting cover on a ringed space"]
theorem existsCover_splitting
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₃.IsFiniteLocallyFree] :
    ∃ (I : Type u) (U : I → Opens X),
      (Opens.grothendieckTopology X).CoversTop U ∧
        ∀ i : I,
          Nonempty
            ((S.map
              (SheafOfModules.Localization.restriction X.ringCatSheaf (U i))).Splitting) := sorry

end AlgebraicGeometry.RingedSpace.Modules.FiniteFreeRetract
