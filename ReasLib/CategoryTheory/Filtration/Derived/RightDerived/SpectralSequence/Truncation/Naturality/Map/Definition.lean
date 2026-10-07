module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Views
public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of truncation-filtration realizations

A map retains the generic realization map and the source-facing page-two and abutment naturality data.
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

/- The generic realization map is the sole owner of resolutions and associations here. -/
/-- A map of truncation-filtration realizations with page-two and abutment naturality. -/
@[stacks 0BKM "map of truncation-filtration right-derived spectral sequences"]
structure Map {K L : DerivedCategory A} (f : K ⟶ L)
    (S : Realization F K) (T : Realization F L) where
  /-- The chosen cochain-map lift between the selected derived representatives. -/
  lift : DerivedCategory.Preimage.Lift f
  /-- The underlying generic map on the selected truncation filtrations. -/
  original :
    RightDerived.SpectralSequence.Realization.Map F
      (CochainComplex.TruncationFiltration.map lift.hom) S.original T.original
  /-- Naturality of the source-facing `E₂` comparison. -/
  pageTwo_hom : ∀ (i : ℕ) (j : ℤ),
    ((CohomologicalSpectralSequence.Renumber.FromZero.map
      original.sequenceMap).hom 2 le_rfl).f
          (Int.ofNat i, j) ≫
          (T.pageTwoIso i j).hom =
      (S.pageTwoIso i j).hom ≫
        (F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f)
  /-- Naturality of the abutment comparison. -/
  target_hom : ∀ n : ℤ,
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap original.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        (Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f

/-- The filtered-model component of a truncation-filtration realization map. -/
@[stacks 0BKM "filtered component of a truncation-filtration realization map"]
noncomputable abbrev Map.filteredMap {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    S.filtered ⟶ T.filtered :=
  m.original.filteredMap

/-- The renumbered spectral-sequence component of a truncation-filtration realization map. -/
@[stacks 0BKM "spectral-sequence component of a truncation-filtration realization map"]
noncomputable abbrev Map.sequenceMap {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
  S.sequence ⟶ T.sequence :=
  CohomologicalSpectralSequence.Renumber.FromZero.map m.original.sequenceMap

/-- The association morphism before page renumbering, owned by the generic realization map. -/
@[stacks 0BKM "association morphism of a truncation-filtration realization map"]
noncomputable abbrev Map.toAssociationHom {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  m.original.toAssociationHom

/-- The chosen lift carried by a truncation-filtration map represents its base derived morphism. -/
@[stacks 0BKM "localization specification carried by a truncation realization map"]
theorem Map.lift_map_eq {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).map m.lift.hom =
      (DerivedCategory.Q.objObjPreimageIso K).hom ≫ f ≫
        (DerivedCategory.Q.objObjPreimageIso L).inv := sorry

/-- The association morphism of a truncation-filtration map has the same component as the
unrenumbered generic realization map. -/
@[simp, stacks 0BKM "spectral-sequence component of a truncation association morphism"]
theorem Map.toAssociationHom_hom {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    m.toAssociationHom.hom = m.original.sequenceMap := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
