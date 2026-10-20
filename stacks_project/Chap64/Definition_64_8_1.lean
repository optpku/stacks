/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap64.Definition_64_8_1_RightExact
public import ReasLib.CategoryTheory.Filtration.Derived.LeftExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 64.8.1 (1). If T : 𝒜 ⥤ₗ ℬ is left exact and 𝒜 has enough injectives,
the filtered derived functor RT : DF⁺(𝒜) ⥤ DF⁺(ℬ) is
`FilteredObject.FiniteDerived.Plus.LeftExact.functor`. After the identification
DF⁺(𝒜) ≌ K⁺(I) of Lemma 64.7.2, the source square with
K⁺(I) --T--> K⁺(Filᶠ(ℬ)) is the Kan-extension unit
`FilteredObject.FiniteDerived.Plus.LeftExact.unit`. The bottom arrow is
`FilteredObject.FiniteDerived.Plus.LeftExact.homotopy`. -/
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Plus.LeftExact.functor
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Plus.LeftExact.unit
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Plus.LeftExact.homotopy

/- Definition 64.8.1 (2). If G : 𝒜 ⥤ᵣ ℬ is right exact and 𝒜 has enough projectives,
the filtered derived functor LG : DF⁻(𝒜) ⥤ DF⁻(ℬ) is
`FilteredObject.FiniteDerived.Minus.RightExact.functor`. The source square with
K⁻(P) --G--> K⁻(Filᶠ(ℬ)) is
`FilteredObject.FiniteDerived.Minus.RightExact.diagramIso`. The bottom arrow is
`FilteredObject.FiniteDerived.Minus.RightExact.homotopy`. -/
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Minus.RightExact.functor
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Minus.RightExact.homotopy
@[stacks 03TD] #check @FilteredObject.FiniteDerived.Minus.RightExact.diagramIso
