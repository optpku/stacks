module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Map.Naturality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality squares for truncation-filtration realizations

The source-facing second-page and abutment equations are exposed as `CommSq` objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

namespace Realization.Map

/-- The second-page naturality equation as a bundled square for a truncation filtration. -/
@[stacks 0BKM "second-page naturality square for a truncation filtration"]
theorem pageTwoSq {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (i : ℕ) (j : ℤ) :
    CommSq ((m.sequenceMap.hom 2 le_rfl).f (Int.ofNat i, j))
      (S.pageTwoIso i j).hom (T.pageTwoIso i j).hom
      ((F.rightDerived i).map ((DerivedCategory.homologyFunctor A j).map f)) := sorry

/-- The abutment naturality equation as a bundled square for a truncation filtration. -/
@[stacks 0BKM "abutment naturality square for a truncation filtration"]
theorem targetSq {K L : DerivedCategory A} {f : K ⟶ L}
    {S : Realization F K} {T : Realization F L}
    (m : Map F f S T) (n : ℤ) :
    CommSq (HomologicalComplex.homologyMap (FilteredComplex.underlyingMap m.filteredMap) n)
      (S.targetIso n).hom (T.targetIso n).hom
      ((Functor.RightDerived.Homotopy.cohomologyFunctor F n).map f) := sorry

end Realization.Map

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation
