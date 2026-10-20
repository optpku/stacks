module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.Morphism

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism

-- Explicit argument mode prevents implicit lambdas from consuming the morphism-property binders.
#check (@AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism.locallyBoundedFiniteLocallyFree :
    ∀ {X : RingedSpace.{u}}, MorphismProperty (ModuleDerived X))

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism.HasLocallyBoundedFiniteLocallyFree :
    ∀ {X : RingedSpace.{u}} {E₁ E₂ : ModuleDerived X} (α : E₁ ⟶ E₂), Prop)

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism.hasLocallyBoundedFiniteLocallyFree_iff :
    ∀ {X : RingedSpace.{u}} {E₁ E₂ : ModuleDerived X} (α : E₁ ⟶ E₂),
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
                  ObjectProperty X.Modules) (K₂.X i))

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism.HasLocallyBoundedFiniteLocallyFree.of :
    ∀ {X : RingedSpace.{u}} {E₁ E₂ : ModuleDerived X} {α : E₁ ⟶ E₂}
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
          ObjectProperty X.Modules) (K₂.X i)),
    HasLocallyBoundedFiniteLocallyFree α)

#check (AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism.locallyBoundedFiniteLocallyFree_respectsIso :
    ∀ {X : RingedSpace.{u}},
    (locallyBoundedFiniteLocallyFree : MorphismProperty (ModuleDerived X)).RespectsIso)

end AlgebraicGeometry.RingedSpace.ModuleDerived.Morphism
