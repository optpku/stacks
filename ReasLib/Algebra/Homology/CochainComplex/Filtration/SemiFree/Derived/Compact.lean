module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.SemiFree.Derived

@[expose] public section

/-!
# Compact Objects and Semi-Free Filtrations

This leaf records factorization consequences of compactness for semi-free
filtrations and their finite-support subfiltrations.
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

/-- A map into a stage of a semi-free filtration factors through a finite-support subfiltration. -/
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
finite-support subfiltration. -/
@[stacks 09R2]
theorem exists_factorization_through_finiteSubfiltration
    (E : DerivedCategory (ModuleCat A))
    (hE : IsCompactObject E)
    {P : ModuleCat.DGMod A} (F : SemiFreeFiltration P)
    (f : E ⟶ DerivedCategory.Q.obj P) :
    ∃ (F' : FiniteSummandSubfiltration F)
      (g : E ⟶ DerivedCategory.Q.obj F'.obj),
      g ≫ DerivedCategory.Q.map F'.subobject.arrow = f := sorry

end CochainComplex
