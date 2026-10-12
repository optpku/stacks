/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Injective
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

/- Lemma 20.8.1 (01EA): an injective `𝒪_X`-module has surjective restriction maps on sections
along inclusions of open subsets.  The reusable owner exposes both the module-sheaf map and its
underlying additive-sheaf presentation. -/
@[stacks 01EA "restriction of sections of an injective module sheaf"]
#check @AlgebraicGeometry.RingedSpace.Modules.restriction_surjective_of_injective

#check @AlgebraicGeometry.RingedSpace.Modules.underlying_restriction_surjective_of_injective
#check @SheafOfModules.restriction_surjective_of_injective

end
