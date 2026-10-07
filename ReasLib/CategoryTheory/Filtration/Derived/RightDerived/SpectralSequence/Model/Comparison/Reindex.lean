module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Model.Comparison.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Reindexing filtered right-derived comparisons

Compatibility of selected model comparisons is invariant under equality of source morphisms.
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

namespace Model.Comparison.IsCompatible

/-- Reindexing the source morphism of a resolution map preserves compatibility of the chosen
model comparisons. -/
@[stacks 0BKK "reindexing filtered right-derived model comparisons"]
theorem reindex {K L : FilteredComplex A} {f g : K ⟶ L}
    {R : KInjectiveResolution K} {S : KInjectiveResolution L}
    {m : KInjectiveResolution.Map f R S} {P : Comparison F R}
    {Q : Comparison F S} (h : f = g) (hm : IsCompatible F m P Q) :
    IsCompatible F (KInjectiveResolution.Map.reindex h m) P Q := sorry

end Model.Comparison.IsCompatible

end CategoryTheory.FilteredComplex.RightDerived

