module

public import ReasLib.CategoryTheory.Filtration.Derived.Preadditive
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Homotopies into Finite Filtered-Injective Complexes

This leaf records the homotopy-level form of filtered-injective orthogonality.  The normalized
homotopy object and its localization-facing consequences remain in `Derived.Preadditive`; this
file provides the concrete cochain-map statement that applications usually need.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

noncomputable section

universe v u

namespace CategoryTheory.FilteredObject.FiniteDerived

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredInjective

/-- Every cochain map from a finite filtered acyclic complex to a bounded-below
complex of finite filtered-injectives is homotopic to zero. -/
@[stacks 05TX]
theorem nullHomotopy
    {K : CochainComplex (FilteredObject.Finite.category C) ℤ}
    (I : CochainComplex.FilteredInjectivePlus C) (α : K ⟶ I.obj.obj)
    (hK : FilteredObject.Finite.Homotopy.acyclic C ((Homotopy.quotient C).obj K)) :
    Nonempty (Homotopy α 0) := sorry

/-- Two maps into a bounded-below finite filtered-injective complex that become homotopic after
precomposition with a finite filtered quasi-isomorphism are homotopic. -/
theorem homotopic_lifts_of_quasiIso
    {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
    {K L : CochainComplex.Plus (FilteredObject.Finite.category 𝒜)}
    (I : CochainComplex.FilteredInjectivePlus 𝒜)
    (α : K.obj ⟶ L.obj)
    (hα : FilteredObject.Finite.CochainComplex.quasiIso 𝒜 α)
    (γ : K.obj ⟶ I) (β₁ β₂ : L.obj ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := sorry

end FilteredInjective

end CategoryTheory.FilteredObject.FiniteDerived
