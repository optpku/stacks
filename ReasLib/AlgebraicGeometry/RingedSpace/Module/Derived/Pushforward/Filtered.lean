/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence

/-!
# Filtered derived pushforward

This file specializes the generic unbounded filtered right-derived spectral-sequence API to
direct image of modules along a morphism of ringed spaces.  The generic owner retains the explicit
resolution and all comparison data; this namespace presents them in derived-pushforward language.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom
open CategoryTheory CategoryTheory.FilteredComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.moduleDerivedPushforward

variable {X Y : RingedSpace.{u}}

namespace Filtered

/-- The filtered direct-image model attached to an explicit filtered K-injective resolution. -/
@[stacks 0FLL "filtered derived-pushforward model"]
noncomputable abbrev model (f : X ⟶ Y) {K : FilteredComplex X.Modules}
    (R : KInjectiveResolution K) : FilteredComplex Y.Modules :=
  RightDerived.model (pushforward f) R

/-- The morphism of filtered direct-image models induced by a morphism of resolutions. -/
@[stacks 0FLL "morphism of filtered derived-pushforward models"]
noncomputable abbrev modelMap (f : X ⟶ Y) {K L : FilteredComplex X.Modules}
    {g : K ⟶ L} {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (m : KInjectiveResolution.Map g R S) : model f R ⟶ model f S :=
  RightDerived.modelMap (pushforward f) m

end Filtered

namespace StageCohomology

/-- In every degree, the derived pushforward cohomology of sufficiently high filtration stages
vanishes. -/
@[stacks 0FLL "eventual vanishing of filtered derived-pushforward cohomology"]
abbrev eventuallyVanishesAbove (f : X ⟶ Y) (K : FilteredComplex X.Modules) : Prop :=
  RightDerived.StageCohomology.eventuallyVanishesAbove (pushforward f) K

/-- In every degree, sufficiently low stages compute the derived pushforward cohomology of the
underlying complex. -/
@[stacks 0FLL "eventual stabilization of filtered derived-pushforward cohomology"]
abbrev eventuallyStabilizesBelow (f : X ⟶ Y) (K : FilteredComplex X.Modules) : Prop :=
  RightDerived.StageCohomology.eventuallyStabilizesBelow (pushforward f) K

end StageCohomology

namespace SpectralSequence

/-- A realization of the unbounded filtered derived-pushforward spectral sequence. -/
@[stacks 0FLL "unbounded filtered derived-pushforward spectral-sequence realization"]
abbrev Realization (f : X ⟶ Y) (K : FilteredComplex X.Modules) :=
  RightDerived.SpectralSequence.Realization (pushforward f) K

namespace Realization

/-- A compatible map between filtered derived-pushforward spectral-sequence realizations. -/
@[stacks 0FLL "map of filtered derived-pushforward spectral-sequence realizations"]
abbrev Map (f : X ⟶ Y) {K L : FilteredComplex X.Modules} (g : K ⟶ L)
    (S : Realization f K) (T : Realization f L) :=
  RightDerived.SpectralSequence.Realization.Map (pushforward f) g S T

/-- The filtered-model component of a map of derived-pushforward realizations. -/
@[stacks 0FLL "filtered component of a derived-pushforward realization map"]
noncomputable abbrev Map.filteredMap {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) :
    S.filtered ⟶ T.filtered :=
  RightDerived.SpectralSequence.Realization.Map.filteredMap (pushforward f) m

/-- The spectral-sequence component of a map of derived-pushforward realizations. -/
@[stacks 0FLL "spectral-sequence component of a derived-pushforward realization map"]
noncomputable abbrev Map.sequenceMap {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) :
    S.sequence ⟶ T.sequence :=
  RightDerived.SpectralSequence.Realization.Map.sequenceMap (pushforward f) m

/-- Maps of derived-pushforward realizations are determined by their resolution components. -/
@[ext, stacks 0FLL "extensionality of derived-pushforward realization maps"]
theorem Map.ext {f : X ⟶ Y} {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} {m n : Map f g S T}
    (h : m.resolutionMap.hom = n.resolutionMap.hom) : m = n := sorry

/-- The identity map of a filtered derived-pushforward realization. -/
@[stacks 0FLL "identity map of a filtered derived-pushforward spectral sequence"]
noncomputable abbrev Map.id {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) : Map f (𝟙 K) S S :=
  RightDerived.SpectralSequence.Realization.Map.id (pushforward f) S

/-- The filtered-model component of the identity derived-pushforward realization map is the
identity. -/
@[simp, stacks 0FLL "identity map of a filtered derived-pushforward spectral sequence"]
theorem Map.id_filteredMap {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) : (Map.id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity derived-pushforward realization map is the
identity. -/
@[simp, stacks 0FLL "identity map of a filtered derived-pushforward spectral sequence"]
theorem Map.id_sequenceMap {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) : (Map.id S).sequenceMap = 𝟙 S.sequence := sorry

/-- The composite of maps of filtered derived-pushforward realizations. -/
@[stacks 0FLL "composition of maps of filtered derived-pushforward spectral sequences"]
noncomputable abbrev Map.comp {f : X ⟶ Y}
    {K L M : FilteredComplex X.Modules} {g : K ⟶ L} {h : L ⟶ M}
    {S : Realization f K} {T : Realization f L} {U : Realization f M}
    (m : Map f g S T) (n : Map f h T U) : Map f (g ≫ h) S U :=
  RightDerived.SpectralSequence.Realization.Map.comp (pushforward f) m n

/-- The filtered-model component of a composite derived-pushforward realization map is the
composite map. -/
@[simp, stacks 0FLL "composition of maps of filtered derived-pushforward spectral sequences"]
theorem Map.comp_filteredMap {f : X ⟶ Y}
    {K L M : FilteredComplex X.Modules} {g : K ⟶ L} {h : L ⟶ M}
    {S : Realization f K} {T : Realization f L} {U : Realization f M}
    (m : Map f g S T) (n : Map f h T U) :
    (Map.comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite derived-pushforward realization map is the
composite map. -/
@[simp, stacks 0FLL "composition of maps of filtered derived-pushforward spectral sequences"]
theorem Map.comp_sequenceMap {f : X ⟶ Y}
    {K L M : FilteredComplex X.Modules} {g : K ⟶ L} {h : L ⟶ M}
    {S : Realization f K} {T : Realization f L} {U : Realization f M}
    (m : Map f g S T) (n : Map f h T U) :
    (Map.comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- Reindex a map of filtered derived-pushforward realizations along an equality of filtered
complex morphisms. -/
@[stacks 0FLL "reindexing maps of filtered derived-pushforward spectral sequences"]
noncomputable abbrev Map.reindex {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g h : K ⟶ L}
    {S : Realization f K} {T : Realization f L}
    (e : g = h) (m : Map f g S T) : Map f h S T :=
  RightDerived.SpectralSequence.Realization.Map.reindex (pushforward f) e m

/-- Reindexing preserves the filtered-model component of a derived-pushforward realization
map. -/
@[simp, stacks 0FLL "reindexing maps of filtered derived-pushforward spectral sequences"]
theorem Map.reindex_filteredMap {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g h : K ⟶ L}
    {S : Realization f K} {T : Realization f L}
    (e : g = h) (m : Map f g S T) :
    (Map.reindex e m).filteredMap = m.filteredMap := sorry

/-- Reindexing preserves the spectral-sequence component of a derived-pushforward realization
map. -/
@[simp, stacks 0FLL "reindexing maps of filtered derived-pushforward spectral sequences"]
theorem Map.reindex_sequenceMap {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g h : K ⟶ L}
    {S : Realization f K} {T : Realization f L}
    (e : g = h) (m : Map f g S T) :
    (Map.reindex e m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing a derived-pushforward realization map along reflexivity leaves it unchanged. -/
@[simp, stacks 0FLL "reindexing maps of filtered derived-pushforward spectral sequences"]
theorem Map.reindex_rfl {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) :
    Map.reindex rfl m = m := sorry

/-- The identity derived-pushforward realization map is a left identity after reindexing the
filtered-complex morphism. -/
@[stacks 0FLL "left identity for maps of filtered derived-pushforward spectral sequences"]
theorem Map.id_comp {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) :
    Map.reindex (Category.id_comp g) (Map.comp (Map.id S) m) = m := sorry

/-- The identity derived-pushforward realization map is a right identity after reindexing the
filtered-complex morphism. -/
@[stacks 0FLL "right identity for maps of filtered derived-pushforward spectral sequences"]
theorem Map.comp_id {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) :
    Map.reindex (Category.comp_id g) (Map.comp m (Map.id T)) = m := sorry

/-- Composition of derived-pushforward realization maps is associative after reindexing the
filtered-complex morphism. -/
@[stacks 0FLL "associativity of maps of filtered derived-pushforward spectral sequences"]
theorem Map.assoc {f : X ⟶ Y}
    {K L M N : FilteredComplex X.Modules}
    {g : K ⟶ L} {h : L ⟶ M} {i : M ⟶ N}
    {S : Realization f K} {T : Realization f L}
    {U : Realization f M} {V : Realization f N}
    (m : Map f g S T) (n : Map f h T U) (k : Map f i U V) :
    Map.reindex (Category.assoc g h i) (Map.comp (Map.comp m n) k) =
      Map.comp m (Map.comp n k) := sorry

/-- The first page of a filtered derived-pushforward realization is the derived pushforward
cohomology of its graded pieces. -/
@[stacks 0FLL "first page of the filtered derived-pushforward spectral sequence"]
noncomputable abbrev pageOneIso {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) (p q : ℤ) :
    (S.sequence.page 1).X (p, q) ≅
      moduleDerivedPushforward.cochainCohomology f (K.gradedPiece p) (p + q) :=
  RightDerived.SpectralSequence.Realization.pageOneIso S p q

/-- The cohomology of the filtered direct-image model is the derived pushforward cohomology of
the underlying complex. -/
@[stacks 0FLL "abutment of the filtered derived-pushforward spectral sequence"]
noncomputable abbrev targetIso {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) (n : ℤ) :
    S.filtered.underlying.homology n ≅
      moduleDerivedPushforward.cochainCohomology f K.underlying n :=
  RightDerived.SpectralSequence.Realization.targetIso S n

/-- Naturality of the first-page derived-pushforward comparison. -/
@[stacks 0FLL "naturality of the first page of the derived-pushforward spectral sequence"]
theorem Map.pageOne_hom {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        moduleDerivedPushforward.cochainCohomologyMap f
          (FilteredComplex.gradedPieceMap g p) (p + q) := sorry

/-- Naturality of the derived-pushforward abutment comparison. -/
@[stacks 0FLL "naturality of the derived-pushforward abutment"]
theorem Map.target_hom {f : X ⟶ Y}
    {K L : FilteredComplex X.Modules} {g : K ⟶ L}
    {S : Realization f K} {T : Realization f L} (m : Map f g S T) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        moduleDerivedPushforward.cochainCohomologyMap f
          (FilteredComplex.underlyingMap g) n := sorry

/-- Every filtered complex admits a derived-pushforward spectral-sequence realization. -/
@[stacks 0FLL]
theorem nonempty (f : X ⟶ Y) (K : FilteredComplex X.Modules) :
    Nonempty (Realization f K) := sorry

/-- A map of filtered complexes admits compatible derived-pushforward spectral-sequence
realizations. -/
@[stacks 0FLL "functoriality"]
theorem existsMap (f : X ⟶ Y) {K L : FilteredComplex X.Modules} (g : K ⟶ L) :
    ∃ (S : Realization f K) (T : Realization f L), Nonempty (Map f g S T) := sorry

/-- Eventual stage vanishing and stabilization make a derived-pushforward realization bounded. -/
@[stacks 0FLL "boundedness of the filtered derived-pushforward spectral sequence"]
theorem isBounded {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) (hvanish : StageCohomology.eventuallyVanishesAbove f K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow f K) :
    S.sequence.IsBounded := sorry

/-- Eventual stage vanishing and stabilization make the induced direct-image cohomology
filtrations finite. -/
@[stacks 0FLL "finite filtration on derived-pushforward cohomology"]
theorem finite {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) (hvanish : StageCohomology.eventuallyVanishesAbove f K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow f K) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Eventual stage vanishing and stabilization imply convergence to derived pushforward
cohomology. -/
@[stacks 0FLL "convergence of the filtered derived-pushforward spectral sequence"]
theorem converges {f : X ⟶ Y} {K : FilteredComplex X.Modules}
    (S : Realization f K) (hvanish : StageCohomology.eventuallyVanishesAbove f K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow f K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end Realization

end SpectralSequence

end AlgebraicGeometry.RingedSpace.moduleDerivedPushforward
