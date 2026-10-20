/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory DerivedCategory.Plus.CohomologyIn
open AlgebraicGeometry.Scheme.ModuleDerived
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe v

variable {X U : Scheme.{v}} {j : U ⟶ X}
variable [IsNoetherian X] [IsNoetherian U] [IsOpenImmersion j]

/- Lemma 48.30.2: the canonical comparison for a Deligne system remains bijective
for every bounded-below complex with coherent cohomology. -/
@[stacks 0G4K] #check
  (@AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem.homColimitToRestriction_bijective_of_plus :
    ∀ {X U : Scheme.{v}} {j : U ⟶ X} [IsNoetherian X] [IsNoetherian U]
      [IsOpenImmersion j]
      (S : AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem j)
      (L : D⁺[SheafOfModules.isCoherent X.ringCatSheaf]),
      Function.Bijective
        (S.homColimitToRestriction.app
          ((ambient (SheafOfModules.isCoherent X.ringCatSheaf)).obj L)))
