module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Identity
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.Composition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing unbounded filtered right-derived realization maps

This file transports realization maps along equal source morphisms and records the resulting category laws.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Functor.RightDerived.Homotopy

noncomputable section

universe w wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace SpectralSequence.Realization

/-- Reindexing a realization map preserves compatibility with the chosen spectral-sequence
associations. -/
@[stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
theorem Map.reindexAssociationCompatible
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    FilteredComplex.Association.IsCompatible S.association T.association
      (modelMap F (KInjectiveResolution.Map.reindex h m.resolutionMap))
      m.sequenceMap := sorry

/-- The association component obtained by reindexing a realization map leaves the
spectral-sequence morphism unchanged. -/
@[stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
noncomputable def Map.reindexAssociationMap
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    FilteredComplex.Association.Hom S.association T.association
      (modelMap F (KInjectiveResolution.Map.reindex h m.resolutionMap)) where
  hom := m.sequenceMap
  compatible := Map.reindexAssociationCompatible F h m

/-- Reindex a map of right-derived realizations along an equality of source morphisms, without
changing either of its concrete morphism components. -/
@[stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
noncomputable def Map.reindex
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) : Map F g S T where
  resolutionMap := KInjectiveResolution.Map.reindex h m.resolutionMap
  comparisonCompatible := Model.Comparison.IsCompatible.reindex F
    h m.comparisonCompatible
  associationMap := Map.reindexAssociationMap F h m

/-- Reindexing preserves the morphism between the chosen resolutions. -/
@[simp, stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
theorem Map.reindex_resolutionMap
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).resolutionMap =
      KInjectiveResolution.Map.reindex h m.resolutionMap := sorry

/-- Reindexing retains the comparison-compatibility proof after changing the source-morphism
index. -/
@[stacks 0BKK "comparison component of a reindexed right-derived realization map"]
theorem Map.reindex_comparisonCompatible
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).comparisonCompatible =
      Model.Comparison.IsCompatible.reindex F h m.comparisonCompatible := sorry

/-- Reindexing retains the association component, up to its dependent filtered-map index. -/
@[stacks 0BKK "association component of a reindexed right-derived realization map"]
theorem Map.reindex_associationMap
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).associationMap = Map.reindexAssociationMap F h m := sorry

/-- Reindexing preserves the filtered-model morphism of a realization map. -/
@[simp, stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
theorem Map.reindex_filteredMap
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).filteredMap = m.filteredMap := sorry

/-- Reindexing preserves the spectral-sequence morphism of a realization map. -/
@[simp, stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
theorem Map.reindex_sequenceMap
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    (Map.reindex F h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing a right-derived realization map preserves its association morphism after
transporting the dependent filtered-map index. -/
@[simp, stacks 0BKK "reindexed association morphism of filtered right-derived realizations"]
theorem Map.toAssociationHom_reindex
    {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (h : f = g) (m : Map F f S T) :
    ((Map.reindex_filteredMap F h m) ▸
      (Map.reindex F h m).toAssociationHom) = m.toAssociationHom := sorry

/-- Reindexing a realization map along reflexivity leaves it unchanged. -/
@[simp, stacks 0BKK "reindexing maps of filtered right-derived spectral sequences"]
theorem Map.reindex_rfl
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F rfl m = m := sorry

/-- Successive reindexings of a realization map combine by transitivity. -/
@[simp, stacks 0BKK "transitivity of filtered realization-map transport"]
theorem Map.reindex_trans
    {K L : FilteredComplex A} {f f' f'' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (e' : f' = f'') (m : Map F f S T) :
    Map.reindex F e' (Map.reindex F e m) = Map.reindex F (e.trans e') m := sorry

/-- Reindexing along an equality and its inverse recovers a realization map. -/
@[simp, stacks 0BKK "inverse filtered realization-map transport"]
theorem Map.reindex_symm
    {K L : FilteredComplex A} {f f' : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (e : f = f') (m : Map F f S T) :
    Map.reindex F e.symm (Map.reindex F e m) = m := sorry

/-- Reindexing the left factor of a composite realization map commutes with composition. -/
@[simp, stacks 0BKK "left-factor filtered realization-map transport"]
theorem Map.reindex_comp_left
    {K L M : FilteredComplex A} {f f' : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : K ⟶ L => k ≫ g) e) (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) n := sorry

/-- Reindexing the right factor of a composite realization map commutes with composition. -/
@[simp, stacks 0BKK "right-factor filtered realization-map transport"]
theorem Map.reindex_comp_right
    {K L M : FilteredComplex A} {f : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg (fun k : L ⟶ M => f ≫ k) e) (Map.comp F m n) =
      Map.comp F m (Map.reindex F e n) := sorry

/-- Reindexing both factors of a composite realization map commutes with composition. -/
@[simp, stacks 0BKK "two-factor filtered realization-map transport"]
theorem Map.reindex_comp
    {K L M : FilteredComplex A} {f f' : K ⟶ L} {g g' : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (e : f = f') (e' : g = g') (m : Map F f S T) (n : Map F g T U) :
    Map.reindex F (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e')
        (Map.comp F m n) =
      Map.comp F (Map.reindex F e m) (Map.reindex F e' n) := sorry

/-- The identity realization map is a left identity after reindexing the source morphism. -/
@[stacks 0BKK "left identity for maps of filtered right-derived spectral sequences"]
theorem Map.id_comp
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.id_comp f) (Map.comp F (Map.id F S) m) = m := sorry

/-- The identity realization map is a right identity after reindexing the source morphism. -/
@[stacks 0BKK "right identity for maps of filtered right-derived spectral sequences"]
theorem Map.comp_id
    {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    Map.reindex F (Category.comp_id f) (Map.comp F m (Map.id F T)) = m := sorry

/-- Composition of realization maps is associative after reindexing the source morphism. -/
@[stacks 0BKK "associativity of maps of filtered right-derived spectral sequences"]
theorem Map.assoc
    {K L M N : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization F K} {T : Realization F L}
    {U : Realization F M} {V : Realization F N}
    (m : Map F f S T) (n : Map F g T U) (k : Map F h U V) :
    Map.reindex F (Category.assoc f g h) (Map.comp F (Map.comp F m n) k) =
      Map.comp F m (Map.comp F n k) := sorry

end SpectralSequence.Realization

end CategoryTheory.FilteredComplex.RightDerived
