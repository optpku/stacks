module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Cotensor
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Relation
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Functoriality
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Relation
public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Equiv

/-!
@stack 0FKJ

# Comparison with cotensor-valued cosimplicial homotopy

This module compares the componentwise and cotensor-valued homotopy relations and transfers
degreewise functoriality to the cotensor presentation. It is the only layer that needs both the
relation API and the cotensor conversion API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe u v u' v'

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]
variable {U V : CosimplicialObject C} {a b : U ⟶ V}

section

variable [HasCotensor (Δ[1] : SSet.{0}) V]

/-- When the displayed `Δ[1]` cotensor exists, the product-free zigzag relation agrees with
canonical cosimplicial homotopy. -/
@[stacks 0FKJ "product-free and cotensor-valued homotopy relations agree"]
theorem DeltaOneHomotopic.iff_homotopic (a b : U ⟶ V) :
    DeltaOneHomotopic a b ↔ Homotopic a b := sorry

/-- A product-free homotopy is promoted to the cotensor-valued relation whenever the displayed
`Δ[1]` cotensor exists. -/
@[stacks 0FKJ "product-free homotopy promotes to cotensor homotopy"]
theorem DeltaOneHomotopic.toHomotopic (h : DeltaOneHomotopic a b) : Homotopic a b := sorry

/-- A cotensor-valued homotopy can be used in the product-free relation without inspecting a
chosen cotensor object. -/
@[stacks 0FKJ "cotensor homotopy descends to product-free homotopy"]
theorem Homotopic.toDeltaOne (h : Homotopic a b) : DeltaOneHomotopic a b := sorry

namespace IsHomotopyEquivalence.cotensor

/-- The product-free and cotensor-valued inverse criteria for a cosimplicial homotopy equivalence
agree when both endpoint cotensors exist. -/
@[stacks 0FKK "cotensor criterion for cosimplicial homotopy equivalence"]
theorem iff_exists_inverse
    {U V : CosimplicialObject C} (f : U ⟶ V)
    [HasCotensor (Δ[1] : SSet.{0}) U]
    [HasCotensor (Δ[1] : SSet.{0}) V] :
    IsHomotopyEquivalence f ↔
      ∃ g : V ⟶ U, Homotopic (f ≫ g) (𝟙 U) ∧ Homotopic (g ≫ f) (𝟙 V) := sorry

end IsHomotopyEquivalence.cotensor

/-- When the displayed `Δ[1]` cotensor exists, the product-free and cotensor-valued directed
homotopy relations agree before taking their equivalence closures. -/
@[stacks 0FKJ "product-free and cotensor-valued directed homotopy relations agree"]
theorem DeltaOneHomotopy.directed.iff_homotopy (a b : U ⟶ V) :
    DeltaOneHomotopy.directed a b ↔ DirectedHomotopy a b := sorry

end

section Functoriality

variable [HasCotensor (Δ[1] : SSet.{0}) V]

/-- Applying a functor to the product-free presentation and then returning to the cotensor
presentation gives the functorial action on cotensor-valued homotopies. -/
@[stacks 019Y "functoriality of cotensor-valued cosimplicial homotopies"]
def Homotopy.whiskerRight (H : Homotopy a b) (F : C ⥤ D)
    [HasCotensor (Δ[1] : SSet.{0}) (V ⋙ F)] :
    Homotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) :=
  ((DeltaOneHomotopy.ofHomotopy H).whiskerRight F).toHomotopy

/-- Applying a functor preserves a directed cotensor-valued homotopy whenever the target
cotensor exists. -/
@[stacks 019Y "functors preserve directed cotensor-valued cosimplicial homotopy"]
theorem DirectedHomotopy.whiskerRight (h : DirectedHomotopy a b) (F : C ⥤ D)
    [HasCotensor (Δ[1] : SSet.{0}) (V ⋙ F)] :
    DirectedHomotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) := sorry

/-- Functors preserve the zigzag cosimplicial homotopy relation whenever the displayed target
cotensor exists. No product-preservation hypothesis on the functor is needed because the relation
has the equivalent product-free presentation. -/
@[stacks 019Y "functors preserve cotensor-valued cosimplicial homotopy"]
theorem Homotopic.whiskerRight (h : Homotopic a b) (F : C ⥤ D)
    [HasCotensor (Δ[1] : SSet.{0}) (V ⋙ F)] :
    Homotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F) := sorry

end Functoriality

end CategoryTheory.CosimplicialObject
