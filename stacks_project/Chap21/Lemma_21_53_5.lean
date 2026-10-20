/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.IdealPowerTensor
import StacksCheckRecall

/-!
Lemma 21.53.5 (tag `094I`).  Finite-type locally constant cohomology after tensoring with the
constant quotient `Λ / I` propagates to every positive ideal-power quotient.  The stage objects
are the concrete `constantIdealQuotientSheaf` tower, and their cohomology is measured using the
coefficient-sensitive `finiteTypeLocallyConstantIdealPowerModule` property from ReasLib.
-/

@[expose] public section

open CategoryTheory

@[stacks 094I]
#check @CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology.tensor_constantIdealPowerQuotient

#check @CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology.tensor_constantIdealPowerQuotient_succ
#check @CategoryTheory.Sheaf.LocallyConstant.FiniteType.Cohomology.finiteTypeLocallyConstantIdealPowerModule
#check @CategoryTheory.constantIdealPowerQuotientSheafSystem
#check @CategoryTheory.constantIdealQuotientSheaf

end
