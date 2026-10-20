/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Compact.FiniteCell
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [CommRing R]
variable (A : CochainDGAlgebra.{u, v} R)
variable (E : DifferentialGradedModule.Derived.Category.{u, v} A)
variable (hE : IsCompactObject E)
variable {P : DifferentialGradedModule.{u, v} A}
variable (F : DifferentialGradedModule.PropertyP.FiniteFiltration A P)
variable (f : E ⟶ (DifferentialGradedModule.Derived.fromModules A).obj P)

/-!
# Lemma 22.36.3 (09R2)

A map from a compact object into a DG-module with a finite property-P filtration factors through
a DG-submodule retaining only finitely many summands in every filtration piece.
-/

@[stacks 09R2] #check
  (DifferentialGradedModule.Derived.exists_factorization_through_finiteSubfiltration
      A E hE F f :
    ∃ (F' : DifferentialGradedModule.PropertyP.FiniteSubfiltration A F.toFiltration)
      (g : E ⟶ (DifferentialGradedModule.Derived.fromModules A).obj F'.obj),
      g ≫ (DifferentialGradedModule.Derived.fromModules A).map F'.subobject.arrow = f)
#check @DifferentialGradedModule.PropertyP.FiniteSubfiltration
#check @DifferentialGradedModule.PropertyP.FiniteSubfiltration.stagePullback
#check @DifferentialGradedModule.PropertyP.FiniteFiltration
