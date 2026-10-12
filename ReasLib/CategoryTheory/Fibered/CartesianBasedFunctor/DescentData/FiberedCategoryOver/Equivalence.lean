/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.DescentData.FiberedCategoryOver.Action
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.IndexedFunctor.FiberedCategoryOver.Equivalence
public import ReasLib.CategoryTheory.Sites.Descent.IndexedFunctor.DescentData.Properties

/-!
# Equivalences on descent data of fibred categories

This module packages full-faithfulness, equivalence, and prestack/stack invariance for the
direct selected-fiber descent-data action.
-/

@[expose] public section

universe t uC vC uS₁ vS₁

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace FiberedCategoryOver.Descent

variable {C : Type uC} [Category.{vC} C]
variable {A B : FiberedCategoryOver.{uC, vC, uS₁, vS₁} C}
variable {ι : Type t} {S : C} {X : ι → C} (a : ∀ i, X i ⟶ S)

/-- A fiberwise-fully-faithful fibred-category morphism induces a fully faithful functor on
descent data. -/
theorem functor.fullyFaithful
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful) :
    Nonempty (functor a F).FullyFaithful := sorry

/-- The equivalence on descent-data hom-sets induced by fiberwise full faithfulness.  The
fiberwise choices are encapsulated here; applications should use the accompanying
characterization theorems. -/
noncomputable def homEquiv
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)
    (D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a) :
    (D₁ ⟶ D₂) ≃
      ((FiberedCategoryOver.Descent.functor a F).obj D₁ ⟶
        (FiberedCategoryOver.Descent.functor a F).obj D₂) :=
  Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor.mapDescentData.homEquivOf
    (Indexed.functor F) a
    (Indexed.functor.fiberwiseFullyFaithful F h) D₁ D₂

/-- The forward descent-data hom equivalence is the morphism action of the direct
descent-data functor. -/
@[simp]
theorem homEquiv.apply
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)
    (D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a)
    (φ : D₁ ⟶ D₂) :
    homEquiv a F h D₁ D₂ φ =
      (FiberedCategoryOver.Descent.functor a F).map φ := sorry

/-- Each component of inverse descent-data hom transport is characterized by mapping back to
the prescribed target component. -/
@[simp]
theorem homEquiv.symm.apply.homMap
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)
    (D₁ D₂ : (Functor.fiberPseudofunctor A.p).DescentData a)
    (ψ : (FiberedCategoryOver.Descent.functor a F).obj D₁ ⟶
      (FiberedCategoryOver.Descent.functor a F).obj D₂) (i : ι) :
    (fiberFunctor F (X i)).map
        (((homEquiv a F h D₁ D₂).symm ψ).hom i) =
      ψ.hom i := sorry

/-- Inverse descent-data hom transport preserves identity morphisms. -/
@[simp]
theorem homEquiv.symm.apply.id
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)
    (D : (Functor.fiberPseudofunctor A.p).DescentData a) :
    (homEquiv a F h D D).symm
        (𝟙 ((FiberedCategoryOver.Descent.functor a F).obj D)) =
      𝟙 D := sorry

/-- Inverse descent-data hom transport preserves composition. -/
theorem homEquiv.symm.apply.comp
    (F : A ⟶ B)
    (h : ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful)
    (D₁ D₂ D₃ : (Functor.fiberPseudofunctor A.p).DescentData a)
    (φ : (FiberedCategoryOver.Descent.functor a F).obj D₁ ⟶
      (FiberedCategoryOver.Descent.functor a F).obj D₂)
    (ψ : (FiberedCategoryOver.Descent.functor a F).obj D₂ ⟶
      (FiberedCategoryOver.Descent.functor a F).obj D₃) :
    (homEquiv a F h D₁ D₃).symm (φ ≫ ψ) =
      (homEquiv a F h D₁ D₂).symm φ ≫
        (homEquiv a F h D₂ D₃).symm ψ := sorry

/-- Fiberwise equivalences make the direct descent-data functor an equivalence, without
requiring a global quasi-inverse of the fibred-category morphism. -/
theorem functor.isEquivalence.ofFiberwise
    (F : A ⟶ B)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    (functor a F).IsEquivalence := sorry

/-- Boundary form: a fibred-category morphism whose underlying based functor is an equivalence
over the base induces an equivalence on every category of selected-fiber descent data. -/
instance functor.isEquivalence.ofBasedEquivalence
    (F : A ⟶ B) [(toBasedFunctor F).IsEquivalence] :
    (functor a F).IsEquivalence := sorry

/-- The forward morphism of a bicategorical equivalence of fibred categories induces an
equivalence on every category of selected-fiber descent data. -/
instance functor.isEquivalence.ofEquivalence
    (e : A ≌ B) :
    (functor a e.hom).IsEquivalence := sorry

/-- Fiberwise equivalences preserve and reflect the prestack condition for an individual
presieve. -/
theorem isPrestackFor_iff_of_fiberwiseEquivalence
    (F : A ⟶ B)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence)
    (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsPrestackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsPrestackFor R := sorry

/-- Fiberwise equivalences preserve and reflect effective descent for an individual
presieve. -/
theorem isStackFor_iff_of_fiberwiseEquivalence
    (F : A ⟶ B)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence)
    (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsStackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsStackFor R := sorry

/-- Fiberwise equivalences preserve and reflect the prestack condition. -/
theorem isPrestack_iff_of_fiberwiseEquivalence
    (F : A ⟶ B)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence)
    (J : GrothendieckTopology C) :
    Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor B.p) J := sorry

/-- Fiberwise equivalences preserve and reflect the stack condition. -/
theorem isStack_iff_of_fiberwiseEquivalence
    (F : A ⟶ B)
    (h : ∀ U : C, (fiberFunctor F U).IsEquivalence)
    (J : GrothendieckTopology C) :
    Pseudofunctor.IsStack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor B.p) J := sorry

/-- Boundary form of prestack invariance for a morphism whose underlying based functor is an
equivalence over the base. -/
theorem isPrestackFor_iff_of_basedEquivalence
    (F : A ⟶ B) [(toBasedFunctor F).IsEquivalence]
    (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsPrestackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsPrestackFor R := sorry

/-- Boundary form of effective-descent invariance for a morphism whose underlying based functor
is an equivalence over the base. -/
theorem isStackFor_iff_of_basedEquivalence
    (F : A ⟶ B) [(toBasedFunctor F).IsEquivalence]
    (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsStackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsStackFor R := sorry

/-- Boundary form of prestack invariance for a morphism whose underlying based functor is an
equivalence over the base. -/
theorem isPrestack_iff_of_basedEquivalence
    (F : A ⟶ B) [(toBasedFunctor F).IsEquivalence]
    (J : GrothendieckTopology C) :
    Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor B.p) J := sorry

/-- Boundary form of stack invariance for a morphism whose underlying based functor is an
equivalence over the base. -/
theorem isStack_iff_of_basedEquivalence
    (F : A ⟶ B) [(toBasedFunctor F).IsEquivalence]
    (J : GrothendieckTopology C) :
    Pseudofunctor.IsStack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor B.p) J := sorry

/-- A bicategorical equivalence of fibred categories preserves and reflects the prestack
condition for an individual presieve. -/
theorem isPrestackFor_iff_of_equivalence
    (e : A ≌ B) (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsPrestackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsPrestackFor R := sorry

/-- A bicategorical equivalence of fibred categories preserves and reflects effective descent
for an individual presieve. -/
theorem isStackFor_iff_of_equivalence
    (e : A ≌ B) (R : Presieve S) :
    (Functor.fiberPseudofunctor A.p).IsStackFor R ↔
      (Functor.fiberPseudofunctor B.p).IsStackFor R := sorry

/-- A bicategorical equivalence of fibred categories preserves and reflects the prestack
condition. -/
theorem isPrestack_iff_of_equivalence
    (e : A ≌ B) (J : GrothendieckTopology C) :
    Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsPrestack (Functor.fiberPseudofunctor B.p) J := sorry

/-- A bicategorical equivalence of fibred categories preserves and reflects the stack
condition. -/
theorem isStack_iff_of_equivalence
    (e : A ≌ B) (J : GrothendieckTopology C) :
    Pseudofunctor.IsStack (Functor.fiberPseudofunctor A.p) J ↔
      Pseudofunctor.IsStack (Functor.fiberPseudofunctor B.p) J := sorry

end FiberedCategoryOver.Descent

end CategoryTheory
