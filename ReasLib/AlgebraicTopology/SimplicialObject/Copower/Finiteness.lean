module

public import ReasLib.AlgebraicTopology.SimplicialObject.Copower.Functor.Bifunctor
public import ReasLib.AlgebraicTopology.SimplicialSet.Objwise
public import ReasLib.CategoryTheory.Limits.FiniteNonempty.Products
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017E

# Finiteness hypotheses for simplicial copowers

This module packages the elementary hypotheses that make a simplicial-set-indexed copower
available from binary coproducts: degreewise finiteness and nonemptiness of the indexing
simplicial set.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

noncomputable section

universe vC uC uS

namespace SSet

/-- The object property of being degreewise finite and having a nonempty set of vertices. -/
@[stacks 017E "degreewise finite nonempty object property"]
abbrev degreewiseFiniteNonempty : ObjectProperty SSet.{uS} :=
  fun U ↦ U.ObjFinite ∧ U.Nonempty

/-- The full subcategory of degreewise finite nonempty simplicial sets. This is the formal
counterpart of the category of finite nonempty simplicial sets used for finite copowers. -/
@[stacks 017E "degreewise finite nonempty simplicial sets"]
abbrev DegreewiseFiniteNonempty := degreewiseFiniteNonempty.FullSubcategory

namespace DegreewiseFiniteNonempty

/-- The inclusion of degreewise finite nonempty simplicial sets into all simplicial sets. -/
@[stacks 017E "inclusion of finite nonempty simplicial sets"]
abbrev inclusion : DegreewiseFiniteNonempty.{uS} ⥤ SSet.{uS} :=
  degreewiseFiniteNonempty.ι

/-- The underlying simplicial set of a degreewise finite nonempty object is objectwise finite. -/
@[stacks 017E "degreewise finite subtype instance"]
instance objFinite (U : DegreewiseFiniteNonempty.{uS}) : U.obj.ObjFinite :=
  U.property.1

/-- A degreewise finite nonempty simplicial set has a nonempty set of vertices. -/
@[stacks 017E "nonempty simplicial-set subtype instance"]
instance nonempty (U : DegreewiseFiniteNonempty.{uS}) : U.obj.Nonempty :=
  U.property.2

end DegreewiseFiniteNonempty

end SSet

namespace CategoryTheory.SimplicialObject.HasCopowers

variable {C : Type uC} [Category.{vC} C]

/-- Objectwise finiteness and the existence of a vertex in `U` supply the degreewise coproducts
required for the simplicial copower `copower U X` for every simplicial object `X`. Mathlib
propagates a vertex to a simplex in every degree. -/
@[stacks 017C "finite nonempty copower existence",
  stacks 017I "finite nonempty copower existence"]
noncomputable instance (priority := 100) ofFiniteNonempty (U : SSet.{uS})
    [HasBinaryCoproducts C] [U.ObjFinite] [U.Nonempty] :
    SimplicialObject.HasCopowers U C where
  hasIndexedCoprod V :=
    { hasCoproduct := fun Δ ↦
        Limits.hasCoproduct_of_finite_of_nonempty C
          (fun _ : U.obj Δ ↦ V.obj Δ) }

namespace OfIndex

/-- Binary coproducts supply copowers along the inclusion of degreewise finite nonempty
simplicial sets. -/
@[stacks 017E "copowers indexed by finite nonempty simplicial sets"]
noncomputable instance degreewiseFiniteNonempty [HasBinaryCoproducts C] :
    SimplicialObject.HasCopowers.OfIndex SSet.DegreewiseFiniteNonempty.inclusion C :=
  ⟨fun U ↦ CategoryTheory.SimplicialObject.HasCopowers.ofFiniteNonempty U.obj⟩

end OfIndex

end CategoryTheory.SimplicialObject.HasCopowers
