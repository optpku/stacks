/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Comparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality squares for stupid-filtration realizations

The source-facing first-page and abutment equations are also available as standard `CommSq`
objects for categorical composition and transport.
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

namespace Realization.Map

/-- The first-page naturality equation as a bundled square for a stupid filtration. -/
@[stacks 0FLK "first-page naturality square for a stupid filtration"]
theorem pageOneSq {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (p : ℤ) (q : ℕ) :
    CommSq ((m.sequenceMap.hom 1 zero_le_one).f (p, Int.ofNat q))
      (S.pageOneIso p q).hom (T.pageOneIso p q).hom
      ((F.rightDerived q).map (f.f p)) := sorry

/-- The abutment naturality equation as a bundled square for a stupid filtration. -/
@[stacks 0FLK "abutment naturality square for a stupid filtration"]
theorem targetSq {K L : CochainComplex A ℤ} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L} (m : Map F f S T) (n : ℤ) :
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n)
      (S.targetIso n).hom (T.targetIso n).hom
      (Functor.RightDerived.Homotopy.cochainCohomologyMap F f n) := sorry

end Realization.Map

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid
