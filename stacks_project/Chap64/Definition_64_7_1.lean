/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Projective
import ReasLib.CategoryTheory.Filtration.FiniteBiproduct
import ReasLib.CategoryTheory.Filtration.FiniteInjective
import ReasLib.CategoryTheory.Filtration.Derived.BoundedLocalization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable [CategoryWithHomology (GradedObject ℤ C)]
variable [HasDerivedCategory (GradedObject ℤ C)]

/- Definition 64.7.1: filtered projectivity is projectivity of every associated graded piece. -/
@[stacks 03TA] #check (CategoryTheory.FilteredObject.IsFilteredProjective : CategoryTheory.FilteredObject C → Prop)

/- (1): Fil(C) is the additive category of decreasing ℤ-filtrations. -/
#check @FilteredObject
#check @DecreasingFiltration
#check (inferInstance : Category (FilteredObject C))
#check (inferInstance : Preadditive (FilteredObject C))
#check (inferInstance : HasZeroObject (FilteredObject C))
#check (inferInstance : HasBinaryBiproducts (FilteredObject C))

/- (2): Filᶠ(C) is the full additive subcategory of finite filtrations. -/
#check @FilteredObject.IsFinite
#check @FilteredObject.Finite.category
#check @FilteredObject.Finite.inclusion
#check @FilteredObject.Finite.preadditive
#check @FilteredObject.Finite.hasBinaryBiproducts

/- (3): a finite filtered object is filtered injective (resp. projective) when
every graded piece is injective (resp. projective). -/
#check @FilteredObject.gradedPiece
#check @FilteredObject.IsFilteredInjective
#check @FilteredObject.Finite.FilteredInjective.property
#check @FilteredObject.IsFilteredProjective

/- (4): Comp(Filᶠ(C)) ⊃ Comp⁺(Filᶠ(C)) and K(Filᶠ(C)) ⊃ K⁺(Filᶠ(C)) are the
usual cochain and homotopy categories. -/
#check CochainComplex (FilteredObject.Finite.category C) ℤ
#check CochainComplex.Plus (FilteredObject.Finite.category C)
#check HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)
#check HomotopyCategory.Plus (FilteredObject.Finite.category C)

/- (5): a morphism of complexes is a filtered quasi-isomorphism when every
associated-graded piece is a quasi-isomorphism. -/
#check @FilteredObject.Finite.AssociatedGraded.cochain
#check @FilteredObject.Finite.CochainComplex.quasiIso
#check @FilteredObject.Finite.Homotopy.quasiIso
#check @FilteredObject.Finite.Homotopy.quasiIso_iff

/- (6): DF(C) (resp. DF⁺(C)) is obtained by inverting filtered
quasi-isomorphisms in K(Filᶠ(C)) (resp. K⁺(Filᶠ(C))). -/
#check @FilteredObject.FiniteDerived.Quotient.Category
#check @FilteredObject.FiniteDerived.Quotient.functor
#check @FilteredObject.FiniteDerived.Quotient.isLocalization
#check @FilteredObject.FiniteDerived.Plus.QuasiIso
#check @FilteredObject.FiniteDerived.Plus.Quotient.canonicalFunctor
#check @FilteredObject.FiniteDerived.Plus.Quotient.canonical_isLocalization
#check @FilteredObject.FiniteDerived.Plus.canonicalCategory
