module

public import ReasLib.CategoryTheory.Filtration.Derived.InjectiveHomotopy
public import ReasLib.CategoryTheory.Filtration.Complex.Finite
import StacksCheckRecall

@[expose] public section

open CategoryTheory HomologicalComplex
open FilteredObject.Finite.CochainComplex
open scoped FilteredObject.Finite

universe v u

/- Exercise 111.30.13: in an abelian category `𝒜`, if `K` and `L` are bounded-below
complexes in `Filᶠ(𝒜)` and `I` is a bounded-below complex of filtered injective objects,
and if `α : K.obj ⟶ L.obj` is a filtered quasi-isomorphism, then any two cochain maps
`β₁, β₂ : L.obj ⟶ I` making the solid triangle with `γ : K.obj ⟶ I` commute up to
homotopy are themselves homotopic. -/
@[stacks 028K] #check
  (CategoryTheory.FilteredObject.FiniteDerived.FilteredInjective.homotopic_lifts_of_quasiIso :
    ∀ {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
      {K L : CochainComplex.Plus (Filᶠ(𝒜))}
      (I : CochainComplex.FilteredInjectivePlus 𝒜)
      (α : K.obj ⟶ L.obj) (hα : quasiIso 𝒜 α)
      (γ : K.obj ⟶ I) (β₁ β₂ : L.obj ⟶ I),
      Nonempty (Homotopy (α ≫ β₁) γ) →
      Nonempty (Homotopy (α ≫ β₂) γ) →
      Nonempty (Homotopy β₁ β₂))
