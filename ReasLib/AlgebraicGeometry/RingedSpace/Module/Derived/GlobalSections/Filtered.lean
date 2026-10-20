module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence

/-!
# Filtered derived global sections

This file specializes the generic unbounded filtered right-derived spectral-sequence API to
global sections of modules on a ringed space.  The resolution, comparison, and association data
remain owned by the generic construction; this namespace supplies the domain-facing names used by
hypercohomology arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.FilteredComplex

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

namespace Filtered

/-- The filtered global-sections model attached to an explicit filtered K-injective resolution. -/
@[stacks 0BKK "filtered derived global-sections model"]
noncomputable abbrev model (X : RingedSpace.{u}) {K : FilteredComplex X.Modules}
    (R : KInjectiveResolution K) : FilteredComplex (ModuleCat (globalSectionsRing X)) :=
  RightDerived.model (moduleGlobalSectionsFunctor X) R

/-- The morphism of filtered global-sections models induced by a morphism of resolutions. -/
@[stacks 0BKK "morphism of filtered derived global-sections models"]
noncomputable abbrev modelMap (X : RingedSpace.{u})
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    (m : KInjectiveResolution.Map f R S) : model X R ⟶ model X S :=
  RightDerived.modelMap (moduleGlobalSectionsFunctor X) m

end Filtered

namespace StageCohomology

/-- In every degree, the hypercohomology of sufficiently high filtration stages vanishes. -/
@[stacks 0BKK "eventual vanishing of stage hypercohomology"]
abbrev eventuallyVanishesAbove (X : RingedSpace.{u})
    (K : FilteredComplex X.Modules) : Prop :=
  RightDerived.StageCohomology.eventuallyVanishesAbove
    (moduleGlobalSectionsFunctor X) K

/-- In every degree, sufficiently low stages compute the hypercohomology of the underlying
complex. -/
@[stacks 0BKK "eventual stabilization of stage hypercohomology"]
abbrev eventuallyStabilizesBelow (X : RingedSpace.{u})
    (K : FilteredComplex X.Modules) : Prop :=
  RightDerived.StageCohomology.eventuallyStabilizesBelow
    (moduleGlobalSectionsFunctor X) K

end StageCohomology

namespace SpectralSequence

/-- A realization of the unbounded filtered hypercohomology spectral sequence of a ringed space. -/
@[stacks 0BKK "unbounded filtered hypercohomology spectral-sequence realization"]
abbrev Realization (X : RingedSpace.{u}) (K : FilteredComplex X.Modules) :=
  RightDerived.SpectralSequence.Realization (moduleGlobalSectionsFunctor X) K

namespace Realization

/-- A compatible map between filtered hypercohomology spectral-sequence realizations. -/
@[stacks 0BKK "map of filtered hypercohomology spectral-sequence realizations"]
abbrev Map (X : RingedSpace.{u}) {K L : FilteredComplex X.Modules} (f : K ⟶ L)
    (S : Realization X K) (T : Realization X L) :=
  RightDerived.SpectralSequence.Realization.Map
    (moduleGlobalSectionsFunctor X) f S T

/-- The filtered-model component of a map of hypercohomology realizations. -/
@[stacks 0BKK "filtered component of a hypercohomology realization map"]
noncomputable abbrev Map.filteredMap {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) :
    S.filtered ⟶ T.filtered :=
  RightDerived.SpectralSequence.Realization.Map.filteredMap
    (moduleGlobalSectionsFunctor X) m

/-- The spectral-sequence component of a map of hypercohomology realizations. -/
@[stacks 0BKK "spectral-sequence component of a hypercohomology realization map"]
noncomputable abbrev Map.sequenceMap {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) :
    S.sequence ⟶ T.sequence :=
  RightDerived.SpectralSequence.Realization.Map.sequenceMap
    (moduleGlobalSectionsFunctor X) m

/-- Maps of hypercohomology realizations are determined by their resolution components. -/
@[ext, stacks 0BKK "extensionality of hypercohomology realization maps"]
theorem Map.ext {X : RingedSpace.{u}} {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} {m n : Map X f S T}
    (h : m.resolutionMap.hom = n.resolutionMap.hom) : m = n := sorry

/-- The identity map of a filtered hypercohomology realization. -/
@[stacks 0BKK "identity map of a filtered hypercohomology spectral sequence"]
noncomputable abbrev Map.id {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) : Map X (𝟙 K) S S :=
  RightDerived.SpectralSequence.Realization.Map.id (moduleGlobalSectionsFunctor X) S

/-- The filtered-model component of the identity hypercohomology realization map is the
identity. -/
@[simp, stacks 0BKK "identity map of a filtered hypercohomology spectral sequence"]
theorem Map.id_filteredMap {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) : (Map.id S).filteredMap = 𝟙 S.filtered := sorry

/-- The spectral-sequence component of the identity hypercohomology realization map is the
identity. -/
@[simp, stacks 0BKK "identity map of a filtered hypercohomology spectral sequence"]
theorem Map.id_sequenceMap {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) : (Map.id S).sequenceMap = 𝟙 S.sequence := sorry

/-- The composite of maps of filtered hypercohomology realizations. -/
@[stacks 0BKK "composition of maps of filtered hypercohomology spectral sequences"]
noncomputable abbrev Map.comp {X : RingedSpace.{u}}
    {K L M : FilteredComplex X.Modules} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {T : Realization X L} {U : Realization X M}
    (m : Map X f S T) (n : Map X g T U) : Map X (f ≫ g) S U :=
  RightDerived.SpectralSequence.Realization.Map.comp
    (moduleGlobalSectionsFunctor X) m n

/-- The filtered-model component of a composite hypercohomology realization map is the
composite map. -/
@[simp, stacks 0BKK "composition of maps of filtered hypercohomology spectral sequences"]
theorem Map.comp_filteredMap {X : RingedSpace.{u}}
    {K L M : FilteredComplex X.Modules} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {T : Realization X L} {U : Realization X M}
    (m : Map X f S T) (n : Map X g T U) :
    (Map.comp m n).filteredMap = m.filteredMap ≫ n.filteredMap := sorry

/-- The spectral-sequence component of a composite hypercohomology realization map is the
composite map. -/
@[simp, stacks 0BKK "composition of maps of filtered hypercohomology spectral sequences"]
theorem Map.comp_sequenceMap {X : RingedSpace.{u}}
    {K L M : FilteredComplex X.Modules} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization X K} {T : Realization X L} {U : Realization X M}
    (m : Map X f S T) (n : Map X g T U) :
    (Map.comp m n).sequenceMap = m.sequenceMap ≫ n.sequenceMap := sorry

/-- Reindex a map of filtered hypercohomology realizations along an equality of the underlying
filtered-complex morphisms. -/
@[stacks 0BKK "reindexing maps of filtered hypercohomology spectral sequences"]
noncomputable abbrev Map.reindex {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f g : K ⟶ L}
    {S : Realization X K} {T : Realization X L}
    (h : f = g) (m : Map X f S T) : Map X g S T :=
  RightDerived.SpectralSequence.Realization.Map.reindex
    (moduleGlobalSectionsFunctor X) h m

/-- Reindexing preserves the filtered-model component of a hypercohomology realization map. -/
@[simp, stacks 0BKK "reindexing maps of filtered hypercohomology spectral sequences"]
theorem Map.reindex_filteredMap {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f g : K ⟶ L}
    {S : Realization X K} {T : Realization X L}
    (h : f = g) (m : Map X f S T) :
    (Map.reindex h m).filteredMap = m.filteredMap := sorry

/-- Reindexing preserves the spectral-sequence component of a hypercohomology realization map. -/
@[simp, stacks 0BKK "reindexing maps of filtered hypercohomology spectral sequences"]
theorem Map.reindex_sequenceMap {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f g : K ⟶ L}
    {S : Realization X K} {T : Realization X L}
    (h : f = g) (m : Map X f S T) :
    (Map.reindex h m).sequenceMap = m.sequenceMap := sorry

/-- Reindexing a hypercohomology realization map along reflexivity leaves it unchanged. -/
@[simp, stacks 0BKK "reindexing maps of filtered hypercohomology spectral sequences"]
theorem Map.reindex_rfl {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) :
    Map.reindex rfl m = m := sorry

/-- The identity hypercohomology realization map is a left identity after reindexing. -/
@[stacks 0BKK "left identity for maps of filtered hypercohomology spectral sequences"]
theorem Map.id_comp {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) :
    Map.reindex (Category.id_comp f) (Map.comp (Map.id S) m) = m := sorry

/-- The identity hypercohomology realization map is a right identity after reindexing. -/
@[stacks 0BKK "right identity for maps of filtered hypercohomology spectral sequences"]
theorem Map.comp_id {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) :
    Map.reindex (Category.comp_id f) (Map.comp m (Map.id T)) = m := sorry

/-- Composition of hypercohomology realization maps is associative after reindexing. -/
@[stacks 0BKK "associativity of maps of filtered hypercohomology spectral sequences"]
theorem Map.assoc {X : RingedSpace.{u}}
    {K L M N : FilteredComplex X.Modules}
    {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    {S : Realization X K} {T : Realization X L}
    {U : Realization X M} {V : Realization X N}
    (m : Map X f S T) (n : Map X g T U) (k : Map X h U V) :
    Map.reindex (Category.assoc f g h) (Map.comp (Map.comp m n) k) =
      Map.comp m (Map.comp n k) := sorry

/-- The first page of a filtered hypercohomology realization is the hypercohomology of its
graded pieces. -/
@[stacks 0BKK "first page of the filtered hypercohomology spectral sequence"]
noncomputable abbrev pageOneIso {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) (p q : ℤ) :
    (S.sequence.page 1).X (p, q) ≅
      GlobalSections.cochainCohomology X (K.gradedPiece p) (p + q) :=
  RightDerived.SpectralSequence.Realization.pageOneIso S p q

/-- The cohomology of the filtered model is the hypercohomology of the underlying complex. -/
@[stacks 0BKK "abutment of the filtered hypercohomology spectral sequence"]
noncomputable abbrev targetIso {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) (n : ℤ) :
    S.filtered.underlying.homology n ≅
      GlobalSections.cochainCohomology X K.underlying n :=
  RightDerived.SpectralSequence.Realization.targetIso S n

/-- Naturality of the first-page hypercohomology comparison. -/
@[stacks 0BKK "naturality of the first page of the hypercohomology spectral sequence"]
theorem Map.pageOne_hom {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) (p q : ℤ) :
    (m.sequenceMap.hom 1).f (p, q) ≫ (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫
        GlobalSections.cochainCohomologyMap X
          (FilteredComplex.gradedPieceMap f p) (p + q) := sorry

/-- Naturality of the hypercohomology abutment comparison. -/
@[stacks 0BKK "naturality of the hypercohomology abutment"]
theorem Map.target_hom {X : RingedSpace.{u}}
    {K L : FilteredComplex X.Modules} {f : K ⟶ L}
    {S : Realization X K} {T : Realization X L} (m : Map X f S T) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        GlobalSections.cochainCohomologyMap X
          (FilteredComplex.underlyingMap f) n := sorry

/-- Every filtered complex of modules on a ringed space admits a hypercohomology
spectral-sequence realization. -/
@[stacks 0BKK]
theorem nonempty (X : RingedSpace.{u}) (K : FilteredComplex X.Modules) :
    Nonempty (Realization X K) := sorry

/-- A map of filtered complexes admits compatible hypercohomology spectral-sequence
realizations. -/
@[stacks 0BKK "functoriality"]
theorem existsMap (X : RingedSpace.{u}) {K L : FilteredComplex X.Modules} (f : K ⟶ L) :
    ∃ (S : Realization X K) (T : Realization X L), Nonempty (Map X f S T) := sorry

/-- Eventual stage vanishing and stabilization make a hypercohomology realization bounded. -/
@[stacks 0BKK "boundedness of the filtered hypercohomology spectral sequence"]
theorem isBounded {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) (hvanish : StageCohomology.eventuallyVanishesAbove X K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow X K) :
    S.sequence.IsBounded := sorry

/-- Eventual stage vanishing and stabilization make the induced hypercohomology filtrations
finite. -/
@[stacks 0BKK "finite filtration on hypercohomology"]
theorem finite {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) (hvanish : StageCohomology.eventuallyVanishesAbove X K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow X K) :
    FilteredComplex.Cohomology.Filtration.IsFinite S.filtered := sorry

/-- Eventual stage vanishing and stabilization imply convergence to hypercohomology. -/
@[stacks 0BKK "convergence of the filtered hypercohomology spectral sequence"]
theorem converges {X : RingedSpace.{u}} {K : FilteredComplex X.Modules}
    (S : Realization X K) (hvanish : StageCohomology.eventuallyVanishesAbove X K)
    (hstabilize : StageCohomology.eventuallyStabilizesBelow X K) :
    FilteredComplex.Cohomology.Convergence.Converges S.filtered S.sequence := sorry

end Realization

end SpectralSequence

end AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
