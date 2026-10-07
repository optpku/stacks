module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.DeltaOne.Relation
public import ReasLib.CategoryTheory.HomRel.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product-free cosimplicial homotopy equivalences

Specializes the reusable `HomRel.Equiv` API to the product-free `DeltaOneHomotopic` relation.
The comparison with homotopy equivalences of opposite simplicial objects belongs in a separate
bridge module.  The root relation-level owner supplies the standard multiplicative,
isomorphism-stable, and functorial interfaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v u' v'

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D]

/-- A product-free cosimplicial homotopy equivalence is an equivalence modulo the `Δ[1]`
homotopy relation.  Its inverse laws are available as `hom_inv_id` and `inv_hom_id`. -/
@[stacks 019N "cosimplicial homotopy equivalence data"]
abbrev HomotopyEquiv (U V : CosimplicialObject C) :=
  HomRel.Equiv (homotopyRel C) U V

variable (C) in
/-- The morphism property obtained by specializing equivalences modulo a relation to
product-free cosimplicial homotopy. -/
@[stacks 019N "cosimplicial homotopy-equivalence property"]
abbrev homotopyEquivalences : MorphismProperty (CosimplicialObject C) :=
  HomRel.equivalences (homotopyRel C)

/-- A morphism of cosimplicial objects is a product-free homotopy equivalence when it is the
forward morphism of a `HomotopyEquiv`. -/
@[stacks 019N "cosimplicial homotopy equivalence criterion"]
abbrev IsHomotopyEquivalence {U V : CosimplicialObject C} (f : U ⟶ V) : Prop :=
  homotopyEquivalences C f

namespace HomotopyEquiv

variable {U V : CosimplicialObject C}

/-- The type of product-free homotopy self-equivalences is inhabited by the identity. -/
protected instance inhabited (U : CosimplicialObject C) : Inhabited (HomotopyEquiv U U) :=
  ⟨HomRel.Equiv.refl (homotopyRel C) U⟩

/-- The forward morphism of a product-free cosimplicial homotopy equivalence has the corresponding
morphism property. -/
@[stacks 019N "forward map of a cosimplicial homotopy equivalence"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    IsHomotopyEquivalence e.hom := sorry

/-- Applying a functor to a product-free cosimplicial homotopy equivalence gives a product-free
homotopy equivalence. -/
@[stacks 019Y "functoriality of cosimplicial homotopy equivalences"]
def whiskerRight (e : HomotopyEquiv U V) (F : C ⥤ D) :
    HomotopyEquiv (U ⋙ F) (V ⋙ F) :=
  e.map ((Functor.whiskeringRight SimplexCategory C D).obj F)

/-- The forward morphism of a whiskered homotopy equivalence is the whiskered forward morphism. -/
@[simp, stacks 019Y "forward map of a whiskered cosimplicial homotopy equivalence"]
theorem whiskerRight.hom (e : HomotopyEquiv U V) (F : C ⥤ D) :
    (e.whiskerRight F).hom = Functor.whiskerRight e.hom F := sorry

/-- The inverse morphism of a whiskered homotopy equivalence is the whiskered inverse morphism. -/
@[simp, stacks 019Y "inverse map of a whiskered cosimplicial homotopy equivalence"]
theorem whiskerRight.inv (e : HomotopyEquiv U V) (F : C ⥤ D) :
    (e.whiskerRight F).inv = Functor.whiskerRight e.inv F := sorry

end HomotopyEquiv

namespace IsHomotopyEquivalence

/-- A cosimplicial map is a product-free homotopy equivalence exactly when it is the forward
map of structured product-free homotopy-equivalence data. -/
@[stacks 019N "structured cosimplicial homotopy-equivalence criterion"]
theorem iff_exists_equiv {U V : CosimplicialObject C} (f : U ⟶ V) :
    IsHomotopyEquivalence f ↔ ∃ e : HomotopyEquiv U V, e.hom = f := sorry

/-- A cosimplicial map is a product-free homotopy equivalence exactly when it admits a map in
the other direction whose composites are product-free homotopic to the identities. -/
@[stacks 019N "inverse criterion for cosimplicial homotopy equivalences"]
theorem iff_exists_inverse {U V : CosimplicialObject C} (f : U ⟶ V) :
    IsHomotopyEquivalence f ↔
      ∃ g : V ⟶ U, DeltaOneHomotopic (f ≫ g) (𝟙 U) ∧
        DeltaOneHomotopic (g ≫ f) (𝟙 V) := sorry

/-- Applying a functor preserves the morphism property of being a product-free cosimplicial
homotopy equivalence. -/
@[stacks 019Y "functoriality of the cosimplicial homotopy-equivalence property"]
theorem whiskerRight {U V : CosimplicialObject C} {f : U ⟶ V}
    (hf : IsHomotopyEquivalence f) (F : C ⥤ D) :
    IsHomotopyEquivalence (Functor.whiskerRight f F) := sorry

end IsHomotopyEquivalence

end CategoryTheory.CosimplicialObject
