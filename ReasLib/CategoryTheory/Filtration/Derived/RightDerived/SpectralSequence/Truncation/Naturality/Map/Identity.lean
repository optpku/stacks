module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Definition
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Identity maps of truncation-filtration realizations

This file defines the identity realization map and computes its retained components.
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

/-- The identity map of a truncation-filtration realization. -/
@[stacks 0BKM "identity map of a truncation-filtration realization"]
noncomputable def Map.id {K : DerivedCategory A} (S : Realization F K) :
    Map F (𝟙 K) S S where
  lift := DerivedCategory.Preimage.Lift.id K
  original :=
    RightDerived.SpectralSequence.Realization.Map.reindex F
      (CochainComplex.TruncationFiltration.map_id
        (DerivedCategory.Q.objPreimage K)).symm
      (RightDerived.SpectralSequence.Realization.Map.id F S.original)
  pageTwo_hom := sorry
  target_hom := sorry

/-- The identity realization map carries the canonical identity lift. -/
@[simp, stacks 0BKM "lift carried by an identity truncation realization map"]
theorem Map.id_lift {K : DerivedCategory A} (S : Realization F K) :
    (Map.id F S).lift = DerivedCategory.Preimage.Lift.id K := sorry

@[simp, stacks 0BKM "identity filtered map of a truncation-filtration realization"]
theorem Map.id_filteredMap {K : DerivedCategory A} (S : Realization F K) :
    (Map.id F S).filteredMap = 𝟙 S.filtered := sorry

@[simp, stacks 0BKM "identity spectral-sequence map of a truncation-filtration realization"]
theorem Map.id_sequenceMap {K : DerivedCategory A} (S : Realization F K) :
    (Map.id F S).sequenceMap = 𝟙 S.sequence := sorry

/-- The original generic map carried by the identity truncation-filtration map. -/
@[simp, stacks 0BKM "identity original map of a truncation realization"]
theorem Map.id_original {K : DerivedCategory A} (S : Realization F K) :
    (Map.id F S).original =
      RightDerived.SpectralSequence.Realization.Map.reindex F
        (CochainComplex.TruncationFiltration.map_id
          (DerivedCategory.Q.objPreimage K)).symm
        (RightDerived.SpectralSequence.Realization.Map.id F S.original) := sorry

/-- The association morphism of the identity truncation-filtration map is the canonical
association identity, after transporting its dependent filtered-map index. -/
@[simp, stacks 0BKM "identity association morphism of a truncation-filtration realization"]
theorem Map.toAssociationHom_id {K : DerivedCategory A} (S : Realization F K) :
    ((Map.id_filteredMap F S) ▸ (Map.id F S).toAssociationHom) =
      FilteredComplex.Association.Hom.id S.association := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
