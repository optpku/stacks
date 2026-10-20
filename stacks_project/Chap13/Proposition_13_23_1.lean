/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.DerivedCategory.InjectiveResolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-!
# Proposition 13.23.1

The canonical target is Mathlib's `DerivedCategory.Plus 𝒜`, not a
chapter-specific presentation.  ReasLib supplies the fully faithful
injective-homotopy embedding and its equivalence criterion.
-/

/- Proposition 13.23.1 (Stacks 013V): bounded-below complexes of injectives
compute the bounded-below derived category. -/
@[stacks 013V] #check @HomotopyCategory.Plus.Injective.toDerived.isEquivalence

#check @HomotopyCategory.Plus.Injective.toDerived
#check @HomotopyCategory.Plus.Injective.toDerived.map_bijective
#synth (HomotopyCategory.Plus.Injective.toDerived 𝒜).Full
#synth (HomotopyCategory.Plus.Injective.toDerived 𝒜).Faithful
#check @HomotopyCategory.Plus.InjectiveResolutionFunctor.toDerived.isEquivalence_of_resolution

end
