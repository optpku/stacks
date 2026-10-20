/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomologicalComplex.Products

/-!
# Products in Derived Categories

@stack 07KC
@stack 0BK6

This leaf owns product constructions in a derived category.  The preservation
API is stated for an explicitly supplied `HasDerivedCategory`, so it works for
any chosen derived localization instead of silently selecting the standard
one.  Coproducts are owned separately by `Limit.Coproducts`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wD v u uJ

namespace CategoryTheory

namespace DerivedCategory.Product

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{wD} C]

/-- Localization to the derived category preserves a product of representative complexes when
that product is exact in the ambient abelian category. -/
@[stacks 0BK6]
instance q_preservesProduct_of_exact {J : Type uJ}
    [HasProductsOfShape J C] [HasExactLimitsOfShape (Discrete J) C]
    (I : J → CochainComplex C ℤ) :
    PreservesLimit (Discrete.functor I) DerivedCategory.Q := sorry

/-- A termwise product of complexes realizes the product of its images whenever the chosen
derived localization preserves that particular product. -/
@[stacks 0BK6, stacks 07D9 "termwise product model"]
noncomputable def fanIsLimit_of_termwise {J : Type uJ}
    (K : J → CochainComplex C ℤ) [HasProduct K]
    [PreservesLimit (Discrete.functor K) DerivedCategory.Q] :
    IsLimit
      (Fan.mk
        (DerivedCategory.Q.obj (∏ᶜ K))
        (fun j ↦ DerivedCategory.Q.map (Pi.π K j))) :=
  Limits.isLimitOfHasProductOfPreservesLimit DerivedCategory.Q K

/-- The discrete diagram of localized representative complexes is isomorphic to the prescribed
derived diagram. -/
@[stacks 0BK6]
noncomputable def modelDiagramIso {J : Type uJ}
    (X : J → DerivedCategory C) (K : J → CochainComplex C ℤ)
    (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    Discrete.functor (fun j ↦ DerivedCategory.Q.obj (K j)) ≅ Discrete.functor X :=
  Discrete.natIso fun j ↦ eK j.as

/-- The fan on a derived diagram obtained from a product of chosen representative complexes. -/
@[stacks 0BK6]
noncomputable def modelFan {J : Type uJ}
    (X : J → DerivedCategory C) (K : J → CochainComplex C ℤ)
    [HasProduct K] (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    Fan X :=
  (Cone.postcompose (modelDiagramIso X K eK).hom).obj
    (Fan.mk (DerivedCategory.Q.obj (∏ᶜ K)) (fun j ↦ DerivedCategory.Q.map (Pi.π K j)))

/-- The projection of the representative-model fan to a chosen derived object. -/
@[stacks 0BK6]
theorem modelFan_proj {J : Type uJ}
    (X : J → DerivedCategory C) (K : J → CochainComplex C ℤ)
    [HasProduct K] (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) (j : J) :
    (modelFan X K eK).proj j =
      DerivedCategory.Q.map (Pi.π K j) ≫ (eK j).hom := sorry

/-- A product of representative complexes realizes the product of their images in the derived
category whenever localization preserves that product. -/
@[stacks 0BK6]
noncomputable def modelFanIsLimit {J : Type uJ}
    (X : J → DerivedCategory C) (K : J → CochainComplex C ℤ)
    [HasProduct K] [PreservesLimit (Discrete.functor K) DerivedCategory.Q]
    (eK : ∀ j, DerivedCategory.Q.obj (K j) ≅ X j) :
    IsLimit (modelFan X K eK) :=
  (IsLimit.postcomposeHomEquiv
    (modelDiagramIso X K eK)
    (Fan.mk (DerivedCategory.Q.obj (∏ᶜ K)) (fun j ↦ DerivedCategory.Q.map (Pi.π K j)))).invFun
    (Limits.isLimitOfHasProductOfPreservesLimit DerivedCategory.Q K)

/-- Exact products of a prescribed discrete shape in an abelian category induce products of
that shape in its derived category. -/
@[stacks 0BK6]
instance hasProductsOfShape_of_exact {J : Type uJ}
    [HasProductsOfShape J C] [HasExactLimitsOfShape (Discrete J) C] :
    HasProductsOfShape J (DerivedCategory C) := sorry

/-- A Grothendieck abelian category has products of every prescribed shape in its derived
category. -/
@[stacks 0BK6, stacks 07D9 "derived products"]
instance hasProductsOfShape_of_grothendieck {J : Type uJ}
    [IsGrothendieckAbelian.{uJ} C] :
    HasProductsOfShape J (DerivedCategory C) := sorry

/-- The canonical comparison from the homology of a termwise product representative to the
product of the derived homology objects. -/
@[stacks 07KC]
noncomputable def homologyProductComparison {J : Type uJ}
    [HasProductsOfShape J C] (p : ℤ) (K : J → CochainComplex C ℤ) :
    (DerivedCategory.homologyFunctor C p).obj (DerivedCategory.Q.obj (∏ᶜ K)) ⟶
      ∏ᶜ fun j ↦ (DerivedCategory.homologyFunctor C p).obj
        (DerivedCategory.Q.obj (K j)) :=
  Pi.lift fun j ↦ (DerivedCategory.homologyFunctor C p).map
    (DerivedCategory.Q.map (Pi.π K j))

/-- The derived homology-product comparison is characterized by its composites with the
product projections. -/
@[stacks 07KC, simp, reassoc (attr := simp)]
theorem homologyProductComparison_π {J : Type uJ}
    [HasProductsOfShape J C] (p : ℤ) (K : J → CochainComplex C ℤ) (j : J) :
    homologyProductComparison p K ≫
        Pi.π (fun k ↦ (DerivedCategory.homologyFunctor C p).obj
          (DerivedCategory.Q.obj (K k))) j =
      (DerivedCategory.homologyFunctor C p).map
        (DerivedCategory.Q.map (Pi.π K j)) := sorry

/-- Exact products make the canonical derived homology-product comparison invertible. -/
@[stacks 07KC]
instance homologyProductComparison_isIso_of_exact {J : Type uJ}
    [HasProductsOfShape J C] [HasExactLimitsOfShape (Discrete J) C]
    (p : ℤ) (K : J → CochainComplex C ℤ) :
    IsIso (homologyProductComparison p K) := sorry

end DerivedCategory.Product

end CategoryTheory
