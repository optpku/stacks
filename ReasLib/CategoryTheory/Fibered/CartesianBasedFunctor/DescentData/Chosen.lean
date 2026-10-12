/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Explicit

/-!
# Selected-cleavage descent-data transport

This module specializes explicit-cleavage transport to the cleavages selected by
`Functor.Cleavage.ofIsFibered`, and provides the fixed-owner equivalence API.
-/

@[expose] public section

universe t uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace CartesianBasedFunctor.Descent.chosen

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

/-- The selected-cleavage descent-data functor induced by a cartesian functor between fibred
projections. -/
noncomputable def functor
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    (fiberPseudofunctor p₁).DescentData a ⥤
      (fiberPseudofunctor p₂).DescentData a :=
  (Indexed.chosen.functor F).mapDescentData a

/-- The selected-cleavage descent-data functor acts on objects componentwise through the fiber
functors. -/
@[simp]
theorem functor.obj
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a) (i : ι) :
    ((functor a F).obj D).obj i =
      (F.fiberFunctor (X i)).obj (D.obj i) := sorry

/-- The selected-cleavage descent-data functor transports overlap morphisms by the selected
reindexing conjugation. -/
@[simp]
theorem functor.obj.hom
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    ((functor a F).obj D).hom
        q f₁ f₂ hf₁ hf₂ =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        f₁ (D.obj i₁)).hom ≫
        (F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        f₂ (D.obj i₂)).inv := sorry

/-- Total-category readout of the selected-cleavage overlap-morphism computation. -/
@[simp]
theorem functor.obj.hom.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (D : (fiberPseudofunctor p₁).DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    (((functor a F).obj D).hom
        q f₁ f₂ hf₁ hf₂).1 =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        f₁ (D.obj i₁)).hom.1 ≫
        ((F.fiberFunctor Y).map (D.hom q f₁ f₂ hf₁ hf₂)).1 ≫
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        f₂ (D.obj i₂)).inv.1 := sorry

/-- The selected-cleavage descent-data functor acts on morphisms componentwise through the fiber
functors. -/
@[simp]
theorem functor.map.hom
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {D₁ D₂ : (fiberPseudofunctor p₁).DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    ((functor a F).map φ).hom i =
      (F.fiberFunctor (X i)).map (φ.hom i) := sorry

/-- Total-category readout of the selected-cleavage descent-morphism computation. -/
@[simp]
theorem functor.map.hom.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    {D₁ D₂ : (fiberPseudofunctor p₁).DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    (((functor a F).map φ).hom i).1 =
      ((F.fiberFunctor (X i)).map (φ.hom i)).1 := sorry

/-- The selected-cleavage descent-data functor of the identity cartesian based functor is the
identity functor. -/
@[simp]
theorem functor.id [p₁.IsFibered] :
    functor a (CartesianBasedFunctor.id p₁) =
      𝟭 ((fiberPseudofunctor p₁).DescentData a) := sorry

/-- The selected-cleavage descent-data functor of a composite cartesian based functor is
successive transport through its factors. -/
@[simp]
theorem functor.comp
    {S₃ : Type uS₃} [Category.{vS₃} S₃] {p₃ : S₃ ⥤ C}
    (F : CartesianBasedFunctor p₁ p₂)
    (G : CartesianBasedFunctor p₂ p₃)
    [p₁.IsFibered] [p₂.IsFibered] [p₃.IsFibered] :
    functor a (F.comp G) =
      functor a F ⋙
        functor a G := sorry

/-- Canonical descent commutes with the selected-cleavage descent-data functor. -/
noncomputable def comparisonIso
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered] :
    (fiberPseudofunctor p₁).toDescentData a ⋙
        functor a F ≅
      F.fiberFunctor S ⋙
        (fiberPseudofunctor p₂).toDescentData a :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.Canonical.Comparison.iso
    (Indexed.chosen.functor F) a

/-- Components of the selected-cleavage canonical-descent comparison are inverse selected
reindexing comparisons. -/
@[simp]
theorem comparisonIso.hom.component
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (x : p₁.Fiber S) (i : ι) :
    ((comparisonIso a F).hom.app x).hom i =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (a i) x).inv := sorry

/-- Total-category readout of a forward selected-cleavage canonical-descent comparison
component. -/
@[simp]
theorem comparisonIso.hom.component.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (x : p₁.Fiber S) (i : ι) :
    (((comparisonIso a F).hom.app x).hom i).1 =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (a i) x).inv.1 := sorry

/-- Inverse components of the selected-cleavage canonical-descent comparison are forward
selected reindexing comparisons. -/
@[simp]
theorem comparisonIso.inv.component
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (x : p₁.Fiber S) (i : ι) :
    ((comparisonIso a F).inv.app x).hom i =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (a i) x).hom := sorry

/-- Total-category readout of an inverse selected-cleavage canonical-descent comparison
component. -/
@[simp]
theorem comparisonIso.inv.component.val
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (x : p₁.Fiber S) (i : ι) :
    (((comparisonIso a F).inv.app x).hom i).1 =
      (Reindex.mapIso F
        (Cleavage.ofIsFibered p₁) (Cleavage.ofIsFibered p₂)
        (a i) x).hom.1 := sorry

/-- Fiberwise full faithfulness makes the selected-cleavage descent-data functor fully
faithful. -/
theorem functor.fullyFaithful
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful) :
    Nonempty (functor a F).FullyFaithful := sorry

/-- The hom-set equivalence induced by fiberwise full faithfulness for the selected-cleavage
descent-data functor. -/
noncomputable def homEquiv
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : (fiberPseudofunctor p₁).DescentData a) :
    (D₁ ⟶ D₂) ≃
      ((functor a F).obj D₁ ⟶
        (functor a F).obj D₂) :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.homEquivOf
    (Indexed.chosen.functor F) a
    (Indexed.chosen.functor.fiberwiseFullyFaithful F h) D₁ D₂

/-- The forward selected-cleavage descent-data hom equivalence is the morphism action of the
descent-data functor. -/
@[simp]
theorem homEquiv.apply
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : (fiberPseudofunctor p₁).DescentData a)
    (φ : D₁ ⟶ D₂) :
    homEquiv a F h D₁ D₂ φ =
      (functor a F).map φ := sorry

/-- Mapping a component of inverse selected-cleavage hom transport recovers the prescribed
target component. -/
@[simp]
theorem homEquiv.symm.apply.homMap
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ : (fiberPseudofunctor p₁).DescentData a)
    (ψ : (functor a F).obj D₁ ⟶
      (functor a F).obj D₂) (i : ι) :
    (F.fiberFunctor (X i)).map
        (((homEquiv a F h D₁ D₂).symm ψ).hom i) =
      ψ.hom i := sorry

/-- Inverse selected-cleavage descent-data hom transport preserves identity morphisms. -/
@[simp]
theorem homEquiv.symm.apply.id
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D : (fiberPseudofunctor p₁).DescentData a) :
    (homEquiv a F h D D).symm
        (𝟙 ((functor a F).obj D)) =
      𝟙 D := sorry

/-- Inverse selected-cleavage descent-data hom transport preserves composition. -/
theorem homEquiv.symm.apply.comp
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, Nonempty (F.fiberFunctor U).FullyFaithful)
    (D₁ D₂ D₃ : (fiberPseudofunctor p₁).DescentData a)
    (φ : (functor a F).obj D₁ ⟶
      (functor a F).obj D₂)
    (ψ : (functor a F).obj D₂ ⟶
      (functor a F).obj D₃) :
    (homEquiv a F h D₁ D₃).symm (φ ≫ ψ) =
      (homEquiv a F h D₁ D₂).symm φ ≫
        (homEquiv a F h D₂ D₃).symm ψ := sorry

/-- Fiberwise equivalences make the selected-cleavage descent-data functor an equivalence,
without requiring a global quasi-inverse over the base. -/
theorem functor.isEquivalence
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    (h : ∀ U : C, (F.fiberFunctor U).IsEquivalence) :
    (functor a F).IsEquivalence := sorry

/-- A possibly universe-changing equivalence over the base induces an equivalence on every
selected-cleavage descent-data category. -/
instance functor.isEquivalence.ofBasedEquivalence
    (F : CartesianBasedFunctor p₁ p₂) [p₁.IsFibered] [p₂.IsFibered]
    [F.toBasedFunctor.IsEquivalence] :
    (functor a F).IsEquivalence := sorry

section FixedOwnerEquivalence

universe uS vS

variable {S₁ S₂ : Type uS} [Category.{vS} S₁] [Category.{vS} S₂]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C}

/-- A bicategorical equivalence of fibred based categories induces an equivalence on
selected-cleavage descent-data categories. -/
instance functor.isEquivalence.ofEquivalence
    (e : BasedCategory.ofFunctor p₁ ≌ BasedCategory.ofFunctor p₂)
    [p₁.IsFibered] [p₂.IsFibered] :
    (functor a (ofEquivalence e)).IsEquivalence := sorry

end FixedOwnerEquivalence

end CartesianBasedFunctor.Descent.chosen

end CategoryTheory
