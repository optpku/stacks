module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of truncation-filtration realization maps

This file composes realization maps and computes the filtered, sequence, and association components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe w wA wB vA vB uA uB uC vC

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- The composite of two maps of truncation-filtration realizations. -/
@[stacks 0BKM "composition of truncation-filtration realization maps"]
noncomputable def Map.comp
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) : Map F (f ≫ g) S U where
  lift := DerivedCategory.Preimage.Lift.comp a.lift b.lift
  original :=
    RightDerived.SpectralSequence.Realization.Map.reindex F
      (CochainComplex.TruncationFiltration.map_comp a.lift.hom b.lift.hom).symm
      (RightDerived.SpectralSequence.Realization.Map.comp F a.original b.original)
  pageTwo_hom := sorry
  target_hom := sorry

/-- The lift carried by a composite realization map is the composite of the carried lifts. -/
@[simp, stacks 0BKM "lift carried by a composite truncation realization map"]
theorem Map.comp_lift
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) :
    (Map.comp F a b).lift = DerivedCategory.Preimage.Lift.comp a.lift b.lift := sorry

@[simp, stacks 0BKM "composite filtered map of truncation-filtration realizations"]
theorem Map.comp_filteredMap
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) :
    (Map.comp F a b).filteredMap = a.filteredMap ≫ b.filteredMap := sorry

@[simp, stacks 0BKM "composite spectral-sequence map of truncation-filtration realizations"]
theorem Map.comp_sequenceMap
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) :
    (Map.comp F a b).sequenceMap = a.sequenceMap ≫ b.sequenceMap := sorry

/-- The original generic map carried by a composite truncation-filtration map. -/
@[simp, stacks 0BKM "composite original map of truncation realizations"]
theorem Map.comp_original
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) :
    (Map.comp F a b).original =
      RightDerived.SpectralSequence.Realization.Map.reindex F
        (CochainComplex.TruncationFiltration.map_comp a.lift.hom b.lift.hom).symm
        (RightDerived.SpectralSequence.Realization.Map.comp F a.original b.original) := sorry

/-- The association morphism of a composite truncation-filtration map is the composite of the
association morphisms, after transporting its dependent filtered-map index. -/
@[simp, stacks 0BKM "composite association morphism of truncation-filtration realizations"]
theorem Map.toAssociationHom_comp
    {K L M : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (a : Map F f S T) (b : Map F g T U) :
    ((Map.comp_filteredMap F a b) ▸ (Map.comp F a b).toAssociationHom) =
      FilteredComplex.Association.Hom.comp a.toAssociationHom b.toAssociationHom := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
