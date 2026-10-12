/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.Explicit
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.PullFunctor
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Properties

/-!
# Change of cleavage for descent data

This module gives the canonical descent-data transport between two cleavages of
the same projection, including its pullback comparison and descent-property
invariance.
-/

@[expose] public section

universe t t' uC vC uS₁ vS₁

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Functor.Cleavage

variable {C : Type uC} [Category.{vC} C]
variable {E : Type uS₁} [Category.{vS₁} E] {p : E ⥤ C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

namespace Descent.change

/-- The canonical change-of-cleavage functor between categories of descent data for the same
projection. Its owner is the identity-on-fibers `Indexed.comparison`. -/
noncomputable def functor
    (χ₁ χ₂ : p.Cleavage) :
    χ₁.toPseudofunctor.DescentData a ⥤
      χ₂.toPseudofunctor.DescentData a :=
  (Indexed.comparison χ₁ χ₂).mapDescentData a

/-- Changing cleavage leaves each component object of a descent datum unchanged. -/
@[simp]
theorem functor.obj
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (i : ι) :
    ((functor a χ₁ χ₂).obj D).obj i =
      D.obj i := sorry

/-- Changing cleavage conjugates overlap morphisms by the canonical comparisons between the
two reindexing choices. -/
@[simp]
theorem functor.obj.hom
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    ((functor a χ₁ χ₂).obj D).hom
        q f₁ f₂ hf₁ hf₂ =
      (Reindex.uniqueIsoApp χ₁ χ₂ f₁ (D.obj i₁)).inv ≫
        D.hom q f₁ f₂ hf₁ hf₂ ≫
      (Reindex.uniqueIsoApp χ₁ χ₂ f₂ (D.obj i₂)).hom := sorry

/-- Total-category readout of the change-of-cleavage overlap-morphism computation. -/
@[simp]
theorem functor.obj.hom.val
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ a i₁ = q) (hf₂ : f₂ ≫ a i₂ = q) :
    (((functor a χ₁ χ₂).obj D).hom
        q f₁ f₂ hf₁ hf₂).1 =
      (Reindex.uniqueIsoApp χ₁ χ₂ f₁ (D.obj i₁)).inv.1 ≫
        (D.hom q f₁ f₂ hf₁ hf₂).1 ≫
      (Reindex.uniqueIsoApp χ₁ χ₂ f₂ (D.obj i₂)).hom.1 := sorry

/-- Changing cleavage leaves the components of a descent-data morphism unchanged. -/
@[simp]
theorem functor.map.hom
    (χ₁ χ₂ : p.Cleavage)
    {D₁ D₂ : χ₁.toPseudofunctor.DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    ((functor a χ₁ χ₂).map φ).hom i =
      φ.hom i := sorry

/-- Total-category readout of the change-of-cleavage descent-morphism computation. -/
@[simp]
theorem functor.map.hom.val
    (χ₁ χ₂ : p.Cleavage)
    {D₁ D₂ : χ₁.toPseudofunctor.DescentData a}
    (φ : D₁ ⟶ D₂) (i : ι) :
    (((functor a χ₁ χ₂).map φ).hom i).1 =
      (φ.hom i).1 := sorry

/-- Changing from a cleavage to itself acts identically on descent data. -/
@[simp]
theorem functor.id
    (χ : p.Cleavage) :
    functor a χ χ =
      𝟭 (χ.toPseudofunctor.DescentData a) := sorry

/-- Successive changes of cleavage on descent data compose to the canonical direct change of
cleavage. -/
@[simp]
theorem functor.comp
    (χ₁ χ₂ χ₃ : p.Cleavage) :
    functor a χ₁ χ₂ ⋙ functor a χ₂ χ₃ =
      functor a χ₁ χ₃ := sorry

section

variable {ι' : Type t'} {S' : C} {X' : ι' → C}
variable (a' : ∀ j, X' j ⟶ S')
variable {α : ι' → ι} {q : S' ⟶ S}
variable {q' : ∀ j, X' j ⟶ X (α j)}
variable (w : ∀ j, q' j ≫ a (α j) = a' j ≫ q)

/-- The canonical change-of-cleavage functor commutes with pullback to another indexing
family. -/
noncomputable def pullFunctorIso
    (χ₁ χ₂ : p.Cleavage) :
    Pseudofunctor.DescentData.pullFunctor χ₁.toPseudofunctor w ⋙
        functor a' χ₁ χ₂ ≅
      functor a χ₁ χ₂ ⋙
        Pseudofunctor.DescentData.pullFunctor χ₂.toPseudofunctor w :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.PullFunctor.Comparison.iso
    (Indexed.comparison χ₁ χ₂) a a' w

/-- Forward components of the change-of-cleavage family-pullback comparison are the canonical
forward reindexing comparisons. -/
@[simp]
theorem pullFunctorIso.hom.component
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    ((pullFunctorIso a a' w χ₁ χ₂).hom.app D).hom j =
      (Reindex.uniqueIsoApp χ₁ χ₂ (q' j) (D.obj (α j))).hom := sorry

/-- Total-category readout of a forward change-of-cleavage family-pullback comparison
component. -/
@[simp]
theorem pullFunctorIso.hom.component.val
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    (((pullFunctorIso a a' w χ₁ χ₂).hom.app D).hom j).1 =
      (Reindex.uniqueIsoApp χ₁ χ₂ (q' j) (D.obj (α j))).hom.1 := sorry

/-- Inverse components of the change-of-cleavage family-pullback comparison are the canonical
inverse reindexing comparisons. -/
@[simp]
theorem pullFunctorIso.inv.component
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    ((pullFunctorIso a a' w χ₁ χ₂).inv.app D).hom j =
      (Reindex.uniqueIsoApp χ₁ χ₂ (q' j) (D.obj (α j))).inv := sorry

/-- Total-category readout of an inverse change-of-cleavage family-pullback comparison
component. -/
@[simp]
theorem pullFunctorIso.inv.component.val
    (χ₁ χ₂ : p.Cleavage)
    (D : χ₁.toPseudofunctor.DescentData a) (j : ι') :
    (((pullFunctorIso a a' w χ₁ χ₂).inv.app D).hom j).1 =
      (Reindex.uniqueIsoApp χ₁ χ₂ (q' j) (D.obj (α j))).inv.1 := sorry

end

/-- Changing cleavage induces an equivalence between the corresponding categories of descent
data. -/
instance functor.isEquivalence
    (χ₁ χ₂ : p.Cleavage) :
    (functor a χ₁ χ₂).IsEquivalence := sorry

/-- The prestack condition for an individual presieve is independent of the chosen
cleavage. -/
theorem isPrestackFor_iff
    (χ₁ χ₂ : p.Cleavage) (R : Presieve S) :
    χ₁.toPseudofunctor.IsPrestackFor R ↔
      χ₂.toPseudofunctor.IsPrestackFor R := sorry

/-- Effective descent for an individual presieve is independent of the chosen cleavage. -/
theorem isStackFor_iff
    (χ₁ χ₂ : p.Cleavage) (R : Presieve S) :
    χ₁.toPseudofunctor.IsStackFor R ↔
      χ₂.toPseudofunctor.IsStackFor R := sorry

/-- The prestack condition is independent of the chosen cleavage. -/
theorem isPrestack_iff
    (χ₁ χ₂ : p.Cleavage) (J : GrothendieckTopology C) :
    Pseudofunctor.IsPrestack χ₁.toPseudofunctor J ↔
      Pseudofunctor.IsPrestack χ₂.toPseudofunctor J := sorry

/-- The stack condition is independent of the chosen cleavage. -/
theorem isStack_iff
    (χ₁ χ₂ : p.Cleavage) (J : GrothendieckTopology C) :
    Pseudofunctor.IsStack χ₁.toPseudofunctor J ↔
      Pseudofunctor.IsStack χ₂.toPseudofunctor J := sorry

end Descent.change

end Functor.Cleavage

end CategoryTheory
