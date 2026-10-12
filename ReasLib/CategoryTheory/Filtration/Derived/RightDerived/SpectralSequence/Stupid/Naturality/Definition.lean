/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor

/-!
# Maps of Stupid-Filtration Right-Derived Spectral Sequences

This file defines the data owner for maps between stupid-filtration realizations and exposes its
filtered, spectral-sequence, and association-morphism components.
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

/-- The association owned by the generic filtered right-derived realization. -/
@[stacks 0FLK "association of a stupid-filtration realization"]
noncomputable abbrev association {K : CochainComplex A ℤ} (S : Realization F K) :
    FilteredComplex.Association S.filtered S.sequence :=
  S.original.association

/-- A map of stupid-filtration realizations, including first-page and abutment naturality. -/
@[stacks 0FLK "map of stupid-filtration right-derived spectral sequences"]
structure Map {K L : CochainComplex A ℤ} (f : K ⟶ L)
    (S : Realization F K) (T : Realization F L) where
  /-- The underlying generic filtered right-derived realization map. -/
  original :
    RightDerived.SpectralSequence.Realization.Map F
      (CochainComplex.Stupid.map f) S.original T.original
  /-- Naturality of the source-facing `E₁` comparison. -/
  pageOne_hom : ∀ (p : ℤ) (q : ℕ),
    (original.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) ≫
        (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫ (F.rightDerived q).map (f.f p)
  /-- Naturality of the abutment comparison. -/
  target_hom : ∀ n : ℤ,
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap original.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        Functor.RightDerived.Homotopy.cochainCohomologyMap F f n

/-- The filtered-model component of a stupid-filtration realization map. -/
@[stacks 0FLK "filtered component of a stupid-filtration realization map"]
noncomputable abbrev Map.filteredMap {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    S.filtered ⟶ T.filtered :=
  m.original.filteredMap

/-- The spectral-sequence component of a stupid-filtration realization map. -/
@[stacks 0FLK "spectral-sequence component of a stupid-filtration realization map"]
noncomputable abbrev Map.sequenceMap {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    S.sequence ⟶ T.sequence :=
  m.original.sequenceMap

/-- The association morphism owned by the generic realization map. -/
@[stacks 0FLK "association morphism of a stupid-filtration realization map"]
noncomputable abbrev Map.toAssociationHom {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    FilteredComplex.Association.Hom S.association T.association m.filteredMap :=
  m.original.toAssociationHom

/-- The association morphism of a stupid-filtration map has the same spectral-sequence
component as the wrapper map. -/
@[simp, stacks 0FLK "spectral-sequence component of a stupid-filtration association morphism"]
theorem Map.toAssociationHom_hom {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) :
    m.toAssociationHom.hom = m.sequenceMap := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
