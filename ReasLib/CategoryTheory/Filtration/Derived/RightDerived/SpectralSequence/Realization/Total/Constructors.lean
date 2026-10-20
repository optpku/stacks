module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Map.OfResolution
public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total.Ext
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructors for total unbounded right-derived realizations

These constructors hide the implementation as a displayed total category.  Objects are built
from a realization over its source filtered complex, and morphisms are built from the canonical
dependent realization-map owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F]

namespace Total

/-- Regard a realization over `K` as an object of the total realization category. -/
@[stacks 0BKK "constructor for a total right-derived realization"]
noncomputable abbrev of {K : FilteredComplex A} (S : Realization F K) :
    Realization.Total F where
  base := K
  obj := S

/-- The base of the total object constructed from a realization is its source filtered complex. -/
@[simp, stacks 0BKK "base computation for a total right-derived realization"]
theorem of_base {K : FilteredComplex A} (S : Realization F K) :
    (of F S).base = K := sorry

/-- The displayed object of the total constructor is the supplied realization. -/
@[simp, stacks 0BKK "displayed computation for a total right-derived realization"]
theorem of_obj {K : FilteredComplex A} (S : Realization F K) :
    (of F S).obj = S := sorry

/-- Build a total right-derived realization directly from an explicit resolution, comparison,
and associated spectral sequence. -/
@[stacks 0BKK "total right-derived realization from explicit resolution data"]
noncomputable abbrev ofResolution
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    Realization.Total F :=
  of F (Realization.ofResolution F R P E)

/-- The base of a total realization built from explicit resolution data is its source filtered
complex. -/
@[simp, stacks 0BKK "base of a total realization from explicit resolution data"]
theorem ofResolution_base
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).base = K := sorry

/-- The displayed realization of `ofResolution` is the realization built from the supplied
resolution data. -/
@[simp, stacks 0BKK "displayed realization from explicit resolution data"]
theorem ofResolution_obj
    {K : FilteredComplex A} (R : KInjectiveResolution K)
    (P : Model.Comparison F R)
    (E : FilteredComplex.AssociatedSpectralSequence (model F R)) :
    (ofResolution F R P E).obj = Realization.ofResolution F R P E := sorry

namespace Hom

/-- Regard a dependent realization map as a morphism in the total realization category. -/
@[stacks 0BKK "constructor for a total right-derived realization map"]
noncomputable abbrev ofMap {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    of F S ⟶ of F T where
  base := f
  displayed := m

/-- The base component of `ofMap` is the supplied filtered-complex map. -/
@[simp, stacks 0BKK "base computation for a total right-derived realization map"]
theorem ofMap_base {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).base = f := sorry

/-- The displayed component of `ofMap` is the supplied realization map. -/
@[simp, stacks 0BKK "displayed computation for a total right-derived realization map"]
theorem ofMap_displayed {K L : FilteredComplex A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Realization.Map F f S T) :
    (ofMap F m).displayed = m := sorry

/-- Build a total realization morphism directly from a resolution map, its comparison
compatibility, and an association morphism. -/
@[stacks 0BKK "total realization map from explicit resolution data"]
noncomputable abbrev ofResolutionMap
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    ofResolution F R P E ⟶ ofResolution F S Q E' :=
  ofMap F (Realization.Map.ofResolutionMap F m hm a)

/-- The base component of a total realization map built from resolution data is the supplied
filtered-complex map. -/
@[simp, stacks 0BKK "base of a total realization map from explicit resolution data"]
theorem ofResolutionMap_base
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).base = f := sorry

/-- The displayed component of `ofResolutionMap` is the realization map built from the supplied
resolution data. -/
@[simp, stacks 0BKK "displayed map from explicit total realization data"]
theorem ofResolutionMap_displayed
    {K L : FilteredComplex A} {f : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {P : Model.Comparison F R} {Q : Model.Comparison F S}
    {E : FilteredComplex.AssociatedSpectralSequence (model F R)}
    {E' : FilteredComplex.AssociatedSpectralSequence (model F S)}
    (m : KInjectiveResolution.Map f R S)
    (hm : Model.Comparison.IsCompatible F m P Q)
    (a : FilteredComplex.Association.Hom E.association E'.association (modelMap F m)) :
    (ofResolutionMap F m hm a).displayed =
      Realization.Map.ofResolutionMap F m hm a := sorry

/-- The total map constructed from an identity realization map is an identity. -/
@[simp, stacks 0BKK "identity computation for total realization-map construction"]
theorem ofMap_id {K : FilteredComplex A} (S : Realization F K) :
    ofMap F (Realization.Map.id F S) = 𝟙 (of F S) := sorry

/-- Construction of total realization maps preserves composition. -/
@[simp, stacks 0BKK "composition computation for total realization-map construction"]
theorem ofMap_comp {K L M : FilteredComplex A} {f : K ⟶ L} {g : L ⟶ M}
    {S : Realization F K} {T : Realization F L} {U : Realization F M}
    (m : Realization.Map F f S T) (n : Realization.Map F g T U) :
    ofMap F (Realization.Map.comp F m n) = ofMap F m ≫ ofMap F n := sorry

/-- Reindexing a dependent realization map does not change the constructed total morphism. -/
@[stacks 0BKK "reindexing computation for total realization-map construction"]
theorem ofMap_reindex {K L : FilteredComplex A} {f g : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (h : f = g)
    (m : Realization.Map F f S T) :
    ofMap F (Realization.Map.reindex F h m) = ofMap F m := sorry

end Hom

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
