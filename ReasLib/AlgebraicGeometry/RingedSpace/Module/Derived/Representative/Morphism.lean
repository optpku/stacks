module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree

/-!
# Locally bounded finite locally free representatives of derived morphisms

This file records when a morphism of derived modules is represented by a morphism between
locally bounded, termwise finite locally free cochain complexes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism

variable {X : RingedSpace.{u}}

/-- The morphism property of derived maps represented by a cochain map between locally bounded,
termwise finite locally free complexes. -/
def locallyBoundedFiniteLocallyFree : MorphismProperty (ModuleDerived X) :=
  fun E₁ E₂ α ↦ ∃ (K₁ K₂ : CochainComplex X.Modules ℤ) (a : K₁ ⟶ K₂)
    (e₁ : DerivedCategory.Q.obj K₁ ≅ E₁) (e₂ : DerivedCategory.Q.obj K₂ ≅ E₂),
      α = e₁.inv ≫ DerivedCategory.Q.map a ≫ e₂.hom ∧
        CochainComplex.IsLocallyBoundedAbove K₁ ∧
        CochainComplex.IsLocallyBoundedBelow K₁ ∧
        CochainComplex.IsLocallyBoundedAbove K₂ ∧
        CochainComplex.IsLocallyBoundedBelow K₂ ∧
        ∀ i : ℤ,
          (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
              ObjectProperty X.Modules) (K₁.X i) ∧
            (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
              ObjectProperty X.Modules) (K₂.X i)

/-- A derived morphism has a locally bounded finite locally free representative when it belongs
to `locallyBoundedFiniteLocallyFree`. -/
abbrev HasLocallyBoundedFiniteLocallyFree
    {E₁ E₂ : ModuleDerived X} (α : E₁ ⟶ E₂) : Prop :=
  locallyBoundedFiniteLocallyFree α

/-- The expanded characterization of a derived morphism admitting a locally bounded finite
locally free representative. -/
theorem hasLocallyBoundedFiniteLocallyFree_iff {E₁ E₂ : ModuleDerived X} (α : E₁ ⟶ E₂) :
    HasLocallyBoundedFiniteLocallyFree α ↔
      ∃ (K₁ K₂ : CochainComplex X.Modules ℤ) (a : K₁ ⟶ K₂)
        (e₁ : DerivedCategory.Q.obj K₁ ≅ E₁) (e₂ : DerivedCategory.Q.obj K₂ ≅ E₂),
          α = e₁.inv ≫ DerivedCategory.Q.map a ≫ e₂.hom ∧
            CochainComplex.IsLocallyBoundedAbove K₁ ∧
            CochainComplex.IsLocallyBoundedBelow K₁ ∧
            CochainComplex.IsLocallyBoundedAbove K₂ ∧
            CochainComplex.IsLocallyBoundedBelow K₂ ∧
            ∀ i : ℤ,
              (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
                  ObjectProperty X.Modules) (K₁.X i) ∧
                (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
                  ObjectProperty X.Modules) (K₂.X i) := sorry

namespace HasLocallyBoundedFiniteLocallyFree

/-- Explicit locally bounded finite locally free representatives and a compatible cochain map
give a representative of a derived morphism. -/
theorem of {E₁ E₂ : ModuleDerived X} {α : E₁ ⟶ E₂}
    (K₁ K₂ : CochainComplex X.Modules ℤ) (a : K₁ ⟶ K₂)
    (e₁ : DerivedCategory.Q.obj K₁ ≅ E₁) (e₂ : DerivedCategory.Q.obj K₂ ≅ E₂)
    (hα : α = e₁.inv ≫ DerivedCategory.Q.map a ≫ e₂.hom)
    (h₁Above : CochainComplex.IsLocallyBoundedAbove K₁)
    (h₁Below : CochainComplex.IsLocallyBoundedBelow K₁)
    (h₂Above : CochainComplex.IsLocallyBoundedAbove K₂)
    (h₂Below : CochainComplex.IsLocallyBoundedBelow K₂)
    (hFree : ∀ i : ℤ,
      (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
          ObjectProperty X.Modules) (K₁.X i) ∧
        (SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) :
          ObjectProperty X.Modules) (K₂.X i)) :
    HasLocallyBoundedFiniteLocallyFree α := sorry

end HasLocallyBoundedFiniteLocallyFree

/-- Having a locally bounded finite locally free representative is invariant under isomorphisms
of the source and target derived modules. -/
instance locallyBoundedFiniteLocallyFree_respectsIso :
    (locallyBoundedFiniteLocallyFree :
      MorphismProperty (ModuleDerived X)).RespectsIso := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism
