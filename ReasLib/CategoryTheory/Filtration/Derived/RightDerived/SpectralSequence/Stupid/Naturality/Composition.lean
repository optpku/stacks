/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Definition

/-!
# Identity and Composition of Stupid-Filtration Realization Maps

This file defines identity and composition operations for maps of stupid-filtration realizations
and records their filtered, spectral-sequence, and association-morphism computations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization

/-- The identity map of a stupid-filtration realization. -/
@[stacks 0FLK "identity map of a stupid-filtration realization"]
noncomputable def Map.id {K : CochainComplex A ℤ} (S : Realization F K) :
    Map F (𝟙 K) S S where
  original :=
    RightDerived.SpectralSequence.Realization.Map.reindex F
      (CochainComplex.Stupid.map_id K).symm
      (RightDerived.SpectralSequence.Realization.Map.id F S.original)
  pageOne_hom := sorry
  target_hom := sorry

/-- The filtered component of an identity stupid-filtration realization map is the identity. -/
@[simp, stacks 0FLK "identity filtered map of a stupid-filtration realization"]
theorem Map.id_filteredMap {K : CochainComplex A ℤ} (S : Realization F K) :
    (Map.id F S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of an identity stupid-filtration realization map is the
identity. -/
@[simp, stacks 0FLK "identity spectral-sequence map of a stupid-filtration realization"]
theorem Map.id_sequenceMap {K : CochainComplex A ℤ} (S : Realization F K) :
    (Map.id F S).sequenceMap = 𝟙 S.sequence := sorry

/-- The original generic map carried by the identity stupid-filtration map. -/
@[simp, stacks 0FLK "identity original map of a stupid realization"]
theorem Map.id_original {K : CochainComplex A ℤ} (S : Realization F K) :
    (Map.id F S).original =
      RightDerived.SpectralSequence.Realization.Map.reindex F
        (CochainComplex.Stupid.map_id K).symm
        (RightDerived.SpectralSequence.Realization.Map.id F S.original) := sorry

/-- The association morphism of an identity stupid-filtration map is the canonical identity. -/
@[simp, stacks 0FLK "identity computation for a stupid-filtration association morphism"]
theorem Map.toAssociationHom_id {K : CochainComplex A ℤ} (S : Realization F K) :
    ((Map.id_filteredMap F S) ▸ (Map.id F S).toAssociationHom) =
      FilteredComplex.Association.Hom.id S.association := sorry

/-- The composite of two maps of stupid-filtration realizations. -/
@[stacks 0FLK "composition of stupid-filtration realization maps"]
noncomputable def Map.comp
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) : Map F (f ≫ g) S U where
  original :=
    RightDerived.SpectralSequence.Realization.Map.reindex F
      (CochainComplex.Stupid.map_comp f g).symm
      (RightDerived.SpectralSequence.Realization.Map.comp F m.original n.original)
  pageOne_hom := sorry
  target_hom := sorry

/-- The filtered component of a composite is the composite of the filtered components. -/
@[simp, stacks 0FLK "composite filtered map of stupid-filtration realizations"]
theorem Map.comp_filteredMap
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite is the composite of the spectral-sequence
components. -/
@[simp, stacks 0FLK "composite spectral-sequence map of stupid-filtration realizations"]
theorem Map.comp_sequenceMap
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- The original generic map carried by a composite stupid-filtration map. -/
@[simp, stacks 0FLK "composite original map of stupid realizations"]
theorem Map.comp_original
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    (Map.comp F m n).original =
      RightDerived.SpectralSequence.Realization.Map.reindex F
        (CochainComplex.Stupid.map_comp f g).symm
        (RightDerived.SpectralSequence.Realization.Map.comp F m.original n.original) := sorry

/-- The association morphism of a composite stupid-filtration map is the composite association
morphism. -/
@[simp, stacks 0FLK "composition computation for a stupid-filtration association morphism"]
theorem Map.toAssociationHom_comp
    {K L M : CochainComplex A ℤ} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Map F f S T) (n : Map F g T U) :
    ((Map.comp_filteredMap F m n) ▸ (Map.comp F m n).toAssociationHom) =
      FilteredComplex.Association.Hom.comp m.toAssociationHom n.toAssociationHom := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
