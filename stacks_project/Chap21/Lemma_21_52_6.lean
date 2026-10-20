/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Compact.WeaklyContractible
import StacksCheckRecall

/-!
Lemma 21.52.6 (tag `094E`).  Quasi-compactness and weak contractibility of `U` imply compactness
of the degree-zero localized generator.  The vanishing and coproduct steps are reusable
`ModuleCohomology` bridges, and the chapter entry is only their source-labelled recall.
-/

@[expose] public section

open CategoryTheory

@[stacks 094E]
#check @RingedSite.Hom.ModuleDerived.LocalizedGenerator.isCompactObject_of_quasiCompact_weaklyContractible

#check @RingedSite.Hom.ModuleCohomology.hasDimensionLE_zero_of_weaklyContractible
#check @RingedSite.Hom.ModuleCohomology.hasFiniteDimension_of_weaklyContractible
#check @RingedSite.Hom.ModuleCohomology.preservesCoproducts_of_quasiCompact_weaklyContractible

end
