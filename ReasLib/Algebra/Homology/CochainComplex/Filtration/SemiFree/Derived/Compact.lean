/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Derived

@[expose] public section

/-!
# Compact Objects and Semi-Free Filtrations

This leaf records factorization consequences of compactness for semi-free
filtrations and their finite-support subfiltrations.

The coefficients here are an ordinary ring, viewed in degree zero. The finite-support
factorization combines stage factorization with this specialization of Stacks tag 09R2.
The general DG-algebra statement is
`DifferentialGradedModule.Derived.exists_factorization_through_finiteSubfiltration`.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape DerivedCategory

noncomputable section

universe u

namespace CochainComplex

variable {A : Type u} [Ring A]

open SemiFreeFiltration

/-- A map from a compact derived object into a semi-free complex factors through one filtration
stage. -/
theorem exists_factorization_through_semiFreeStage
    (E : DerivedCategory (ModuleCat A))
    (hE : IsCompactObject E)
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P)
    (f : E ⟶ DerivedCategory.Q.obj P) :
    ∃ n : ℕ, ∃ ψ : E ⟶ DerivedCategory.Q.obj (F.stage n),
      ψ ≫ DerivedCategory.Q.map (F.coconeApp n) = f := sorry

/-- A map into a stage of a semi-free filtration factors through a finite-support subfiltration
whose stages are intersections with the ambient stages and whose quotient maps retain the chosen
finite subsets of ambient summands. -/
theorem exists_factorization_through_finiteSubfiltration_of_stage
    (E : DerivedCategory (ModuleCat A))
    (hE : IsCompactObject E)
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P) (n : ℕ)
    (f : E ⟶ DerivedCategory.Q.obj (F.stage n)) :
    ∃ (F' : FiniteSummandSubfiltration F)
      (g : E ⟶ DerivedCategory.Q.obj F'.obj),
      g ≫ DerivedCategory.Q.map F'.subobject.arrow =
        f ≫ DerivedCategory.Q.map (F.coconeApp n) := sorry

/-- Every map from a compact derived object into a semi-free complex factors through a
finite-support subfiltration with actual intersection stages and selected-summand quotient maps.
This is the ordinary-ring cochain specialization of 09R2, combined with stage factorization. -/
@[stacks 09R2 "ordinary-ring cochain specialization and stage factorization"]
theorem exists_factorization_through_finiteSubfiltration
    (E : DerivedCategory (ModuleCat A))
    (hE : IsCompactObject E)
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P)
    (f : E ⟶ DerivedCategory.Q.obj P) :
    ∃ (F' : FiniteSummandSubfiltration F)
      (g : E ⟶ DerivedCategory.Q.obj F'.obj),
      g ≫ DerivedCategory.Q.map F'.subobject.arrow = f := sorry

end CochainComplex
