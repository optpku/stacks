module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Canonical
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.FullyFaithful

/-!
# Explicit-cleavage descent-data transport

This module provides descent-data transport by a cartesian based functor when both
cleavages are supplied explicitly.  It is the choice-free foundation for the
selected-cleavage and change-of-cleavage APIs.
-/

@[expose] public section

universe t uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace CartesianBasedFunctor.Descent.explicit

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

/-- The functor on descent data induced by a cartesian functor and explicit source and target
cleavages. -/
noncomputable def functor
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    χ₁.toPseudofunctor.DescentData a ⥤
      χ₂.toPseudofunctor.DescentData a :=
  (Indexed.explicit.functor F χ₁ χ₂).mapDescentData a

/-- The explicit-cleavage descent-data functor acts on objects componentwise through the fiber
functors. -/
@[simp]
theorem functor.obj
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (i : ι) :
    ((functor a F χ₁ χ₂).obj D).obj i =
      (F.fiberFunctor (X i)).obj (D.obj i) := sorry

/-- The explicit-cleavage descent-data functor transports overlap morphisms by the canonical
reindexing conjugation. -/
@[simp]
theorem functor.obj.hom
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    ((functor a F χ₁ χ₂).obj D).hom
        q f₁ f₂ hf₁ hf₂ =
      (Reindex.mapIso F χ₁ χ₂ f₁ (D.obj i₁)).hom ≫
        (F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (Reindex.mapIso F χ₁ χ₂ f₂ (D.obj i₂)).inv := sorry

/-- Total-category readout of the explicit-cleavage overlap-morphism computation. -/
@[simp]
theorem functor.obj.hom.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    (((functor a F χ₁ χ₂).obj D).hom
        q f₁ f₂ hf₁ hf₂).1 =
      (Reindex.mapIso F χ₁ χ₂ f₁ (D.obj i₁)).hom.1 ≫
        ((F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂)).1 ≫
      (Reindex.mapIso F χ₁ χ₂ f₂ (D.obj i₂)).inv.1 := sorry

/-- The explicit-cleavage descent-data functor acts on morphisms componentwise through the fiber
functors. -/
@[simp]
theorem functor.map.hom
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {D₁ D₂ : χ₁.toPseudofunctor.DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    ((functor a F χ₁ χ₂).map φ).hom i =
      (F.fiberFunctor (X i)).map (φ.hom i) := sorry

/-- Total-category readout of the explicit-cleavage descent-morphism computation. -/
@[simp]
theorem functor.map.hom.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    {D₁ D₂ : χ₁.toPseudofunctor.DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    (((functor a F χ₁ χ₂).map φ).hom i).1 =
      ((F.fiberFunctor (X i)).map (φ.hom i)).1 := sorry

/-- The explicit-cleavage descent-data functor of the identity cartesian based functor is the
identity functor. -/
@[simp]
theorem functor.id
    (χ : p₁.Cleavage) :
    functor a (CartesianBasedFunctor.id p₁) χ χ =
      𝟭 (χ.toPseudofunctor.DescentData a) := sorry

/-- The explicit-cleavage descent-data functor of a composite cartesian based functor is
successive transport through its factors. -/
@[simp]
theorem functor.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) (χ₃ : p₃.Cleavage) :
    functor a (F.comp G) χ₁ χ₃ =
      functor a F χ₁ χ₂ ⋙
        functor a G χ₂ χ₃ := sorry

/-- Canonical descent commutes with the explicit-cleavage descent-data functor. -/
noncomputable def comparisonIso
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    χ₁.toPseudofunctor.toDescentData a ⋙
        functor a F χ₁ χ₂ ≅
      F.fiberFunctor S ⋙
        χ₂.toPseudofunctor.toDescentData a :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.Canonical.Comparison.iso
    (Indexed.explicit.functor F χ₁ χ₂) a

/-- Components of the explicit-cleavage canonical-descent comparison are inverse reindexing
comparisons. -/
@[simp]
theorem comparisonIso.hom.component
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (x : p₁.Fiber S) (i : ι) :
    ((comparisonIso a F χ₁ χ₂).hom.app x).hom i =
      (Reindex.mapIso F χ₁ χ₂ (a i) x).inv := sorry

/-- Total-category readout of a forward explicit-cleavage canonical-descent comparison
component. -/
@[simp]
theorem comparisonIso.hom.component.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (x : p₁.Fiber S) (i : ι) :
    (((comparisonIso a F χ₁ χ₂).hom.app x).hom i).1 =
      (Reindex.mapIso F χ₁ χ₂ (a i) x).inv.1 := sorry

/-- Inverse components of the explicit-cleavage canonical-descent comparison are forward
reindexing comparisons. -/
@[simp]
theorem comparisonIso.inv.component
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (x : p₁.Fiber S) (i : ι) :
    ((comparisonIso a F χ₁ χ₂).inv.app x).hom i =
      (Reindex.mapIso F χ₁ χ₂ (a i) x).hom := sorry

/-- Total-category readout of an inverse explicit-cleavage canonical-descent comparison
component. -/
@[simp]
theorem comparisonIso.inv.component.val
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (x : p₁.Fiber S) (i : ι) :
    (((comparisonIso a F χ₁ χ₂).inv.app x).hom i).1 =
      (Reindex.mapIso F χ₁ χ₂ (a i) x).hom.1 := sorry

/-- Fiberwise full faithfulness makes the explicit-cleavage descent-data functor fully
faithful. -/
theorem functor.fullyFaithful
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful) :
    Nonempty (functor a F χ₁ χ₂).FullyFaithful := sorry

/-- The hom-set equivalence induced by fiberwise full faithfulness of an explicit-cleavage
cartesian based functor.  Fiberwise choices are encapsulated by the accompanying computation
theorems. -/
noncomputable def homEquiv
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : χ₁.toPseudofunctor.DescentData a) :
    (D₁ ⟶ D₂) ≃
      ((functor a F χ₁ χ₂).obj D₁ ⟶
        (functor a F χ₁ χ₂).obj D₂) :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.homEquivOf
    (Indexed.explicit.functor F χ₁ χ₂) a
    (Indexed.explicit.functor.fiberwiseFullyFaithful F χ₁ χ₂ h) D₁ D₂

/-- The forward explicit-cleavage descent-data hom equivalence is the morphism action of the
descent-data functor. -/
@[simp]
theorem homEquiv.apply
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : χ₁.toPseudofunctor.DescentData a)
    (φ : D₁ ⟶ D₂) :
    homEquiv a F χ₁ χ₂ h D₁ D₂ φ =
      (functor a F χ₁ χ₂).map φ := sorry

/-- Mapping a component of inverse explicit-cleavage hom transport recovers the prescribed
target component. -/
@[simp]
theorem homEquiv.symm.apply.homMap
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : χ₁.toPseudofunctor.DescentData a)
    (ψ : (functor a F χ₁ χ₂).obj D₁ ⟶
      (functor a F χ₁ χ₂).obj D₂) (i : ι) :
    (F.fiberFunctor (X i)).map
        (((homEquiv a F χ₁ χ₂ h D₁ D₂).symm ψ).hom i) =
      ψ.hom i := sorry

/-- Inverse explicit-cleavage descent-data hom transport preserves identity morphisms. -/
@[simp]
theorem homEquiv.symm.apply.id
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D : χ₁.toPseudofunctor.DescentData a) :
    (homEquiv a F χ₁ χ₂ h D D).symm
        (𝟙 ((functor a F χ₁ χ₂).obj D)) =
      𝟙 D := sorry

/-- Inverse explicit-cleavage descent-data hom transport preserves composition. -/
theorem homEquiv.symm.apply.comp
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ D₃ : χ₁.toPseudofunctor.DescentData a)
    (φ : (functor a F χ₁ χ₂).obj D₁ ⟶
      (functor a F χ₁ χ₂).obj D₂)
    (ψ : (functor a F χ₁ χ₂).obj D₂ ⟶
      (functor a F χ₁ χ₂).obj D₃) :
    (homEquiv a F χ₁ χ₂ h D₁ D₃).symm (φ ≫ ψ) =
      (homEquiv a F χ₁ χ₂ h D₁ D₂).symm φ ≫
        (homEquiv a F χ₁ χ₂ h D₂ D₃).symm ψ := sorry

/-- Fiberwise equivalences make the explicit-cleavage descent-data functor an equivalence,
without requiring a global quasi-inverse over the base. -/
theorem functor.isEquivalence
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    (h : ∀ U : C, (F.fiberFunctor U).IsEquivalence) :
    (functor a F χ₁ χ₂).IsEquivalence := sorry

/-- A possibly universe-changing equivalence over the base induces an equivalence on every
explicit-cleavage descent-data category. -/
instance functor.isEquivalence.ofBasedEquivalence
    (F : CartesianBasedFunctor p₁ p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage)
    [F.toBasedFunctor.IsEquivalence] :
    (functor a F χ₁ χ₂).IsEquivalence := sorry

section FixedOwnerEquivalence

universe uS vS

variable {S₁ S₂ : Type uS} [Category.{vS} S₁] [Category.{vS} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- A bicategorical equivalence of based categories induces an equivalence on
explicit-cleavage descent-data categories. -/
instance functor.isEquivalence.ofEquivalence
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂)
    (χ₁ : p₁.Cleavage) (χ₂ : p₂.Cleavage) :
    (functor a (ofEquivalence e) χ₁ χ₂).IsEquivalence := sorry

end FixedOwnerEquivalence

end CartesianBasedFunctor.Descent.explicit

end CategoryTheory
