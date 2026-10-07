module

public import stacks_project.Chap64.Definition_64_7_1_Projective
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

/- Definition 64.7.1 (1): Fil(C) is the additive category of decreasing ℤ-filtrations. -/
@[stacks 03TA] #check @FilteredObject
@[stacks 03TA] #check @DecreasingFiltration
@[stacks 03TA] #check (inferInstance : Category (FilteredObject C))
@[stacks 03TA] #check (inferInstance : Preadditive (FilteredObject C))
@[stacks 03TA] #check (inferInstance : HasZeroObject (FilteredObject C))
@[stacks 03TA] #check (inferInstance : HasBinaryBiproducts (FilteredObject C))

/- Definition 64.7.1 (2): Filᶠ(C) is the full additive subcategory of finite filtrations. -/
@[stacks 03TA] #check @FilteredObject.IsFinite
@[stacks 03TA] #check @FilteredObject.Finite.category
@[stacks 03TA] #check @FilteredObject.Finite.inclusion
@[stacks 03TA] #check @FilteredObject.Finite.preadditive
@[stacks 03TA] #check @FilteredObject.Finite.hasBinaryBiproducts

/- Definition 64.7.1 (3): a finite filtered object is filtered injective (resp. projective) when
every graded piece is injective (resp. projective). -/
@[stacks 03TA] #check @FilteredObject.gradedPiece
@[stacks 03TA] #check @FilteredObject.IsFilteredInjective
@[stacks 03TA] #check @FilteredObject.Finite.FilteredInjective.property
@[stacks 03TA] #check @FilteredObject.IsFilteredProjective

/- Definition 64.7.1 (4): Comp(Filᶠ(C)) ⊃ Comp⁺(Filᶠ(C)) and K(Filᶠ(C)) ⊃ K⁺(Filᶠ(C)) are the
usual cochain and homotopy categories. -/
@[stacks 03TA] #check CochainComplex (FilteredObject.Finite.category C) ℤ
@[stacks 03TA] #check CochainComplex.Plus (FilteredObject.Finite.category C)
@[stacks 03TA] #check HomotopyCategory (FilteredObject.Finite.category C) (ComplexShape.up ℤ)
@[stacks 03TA] #check HomotopyCategory.Plus (FilteredObject.Finite.category C)

/- Definition 64.7.1 (5): a morphism of complexes is a filtered quasi-isomorphism when every
associated-graded piece is a quasi-isomorphism. -/
@[stacks 03TA] #check @FilteredObject.Finite.AssociatedGraded.cochain
@[stacks 03TA] #check @FilteredObject.Finite.CochainComplex.quasiIso
@[stacks 03TA] #check @FilteredObject.Finite.Homotopy.quasiIso
@[stacks 03TA] #check @FilteredObject.Finite.Homotopy.quasiIso_iff

/- Definition 64.7.1 (6): DF(C) (resp. DF⁺(C)) is obtained by inverting filtered
quasi-isomorphisms in K(Filᶠ(C)) (resp. K⁺(Filᶠ(C))). -/
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Quotient.Category
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Quotient.functor
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Quotient.isLocalization
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Plus.QuasiIso
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Plus.Quotient.canonicalFunctor
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Plus.Quotient.canonical_isLocalization
@[stacks 03TA] #check @FilteredObject.FiniteDerived.Plus.canonicalCategory
