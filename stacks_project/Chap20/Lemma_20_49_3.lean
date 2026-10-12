/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.LocallyFree
import StacksCheckRecall

@[expose] public section

/- Lemma 20.49.3: on a ringed space with local stalk rings, perfect derived modules are exactly
those admitting bounded finite locally free, equivalently bounded finite free, local models. -/
@[stacks 0BCJ]
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.perfect_tfae_localModels

#check @SheafOfModules.CochainComplex.IsBoundedFiniteLocallyFree
#check @SheafOfModules.CochainComplex.IsBoundedFiniteFree
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.finiteLocallyFreeOn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.finiteFreeOn
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.isPerfect_iff_finiteLocallyFree
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.isPerfect_iff_finiteFree
#check @AlgebraicGeometry.RingedSpace.ModuleDerived.LocalModel.finiteLocallyFree_iff_finiteFree
