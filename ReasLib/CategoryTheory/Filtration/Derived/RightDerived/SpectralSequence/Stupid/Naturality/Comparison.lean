/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Definition

/-!
# Comparison Naturality for Stupid-Filtration Realizations

This file provides forward, inverse, and computation forms of first-page and abutment naturality
for maps of stupid-filtration right-derived spectral sequences.
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

/-- The first-page naturality law exposed as a theorem rather than a structure projection. -/
@[reassoc, stacks 0FLK "first-page naturality for a stupid-filtration realization map"]
theorem Map.pageOne_naturality {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p : ℤ) (q : ℕ) :
    (m.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) ≫
        (T.pageOneIso p q).hom =
      (S.pageOneIso p q).hom ≫ (F.rightDerived q).map (f.f p) := sorry

/-- The abutment naturality law exposed as a theorem rather than a structure projection. -/
@[reassoc, stacks 0FLK "abutment naturality for a stupid-filtration realization map"]
theorem Map.target_naturality {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n ≫
        (T.targetIso n).hom =
      (S.targetIso n).hom ≫
        Functor.RightDerived.Homotopy.cochainCohomologyMap F f n := sorry

/-- The inverse first-page comparisons are natural for a stupid-filtration realization map. -/
@[reassoc, stacks 0FLK
  "inverse first-page comparison naturality for a stupid-filtration realization map"]
theorem Map.pageOne_inv_naturality {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p : ℤ) (q : ℕ) :
    (F.rightDerived q).map (f.f p) ≫ (T.pageOneIso p q).inv =
      (S.pageOneIso p q).inv ≫
        (m.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) := sorry

/-- The inverse abutment comparisons are natural for a stupid-filtration realization map. -/
@[reassoc, stacks 0FLK
  "inverse abutment comparison naturality for a stupid-filtration realization map"]
theorem Map.target_inv_naturality {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    Functor.RightDerived.Homotopy.cochainCohomologyMap F f n ≫
        (T.targetIso n).inv =
      (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- The first-page comparison can be inverted to recover the underlying spectral-sequence map. -/
@[reassoc, stacks 0FLK "inverse first-page naturality for a stupid-filtration realization map"]
theorem Map.pageOne_naturality_inv {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p : ℤ) (q : ℕ) :
    (S.pageOneIso p q).hom ≫ (F.rightDerived q).map (f.f p) ≫
        (T.pageOneIso p q).inv =
      (m.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) := sorry

/-- Conjugating the stupid-filtration model page map by the inverse comparisons recovers the
first-page right-derived map. -/
@[reassoc, stacks 0FLK "target-map computation for a stupid-filtration first page"]
theorem Map.pageOne_target_map {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p : ℤ) (q : ℕ) :
    (S.pageOneIso p q).inv ≫
        (m.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q) ≫
      (T.pageOneIso p q).hom =
      (F.rightDerived q).map (f.f p) := sorry

/-- The abutment comparison can be inverted to recover the underlying homology map. -/
@[reassoc, stacks 0FLK "inverse abutment naturality for a stupid-filtration realization map"]
theorem Map.target_naturality_inv {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).hom ≫
        Functor.RightDerived.Homotopy.cochainCohomologyMap F f n ≫
        (T.targetIso n).inv =
      HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n := sorry

/-- Conjugating the stupid-filtration model abutment map by the inverse comparisons recovers the
cochain cohomology map. -/
@[reassoc, stacks 0FLK "target-map computation for a stupid-filtration abutment"]
theorem Map.target_map {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    (S.targetIso n).inv ≫
        HomologicalComplex.homologyMap
          (FilteredComplex.underlyingMap m.filteredMap) n ≫
      (T.targetIso n).hom =
      Functor.RightDerived.Homotopy.cochainCohomologyMap F f n := sorry

end Realization

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
