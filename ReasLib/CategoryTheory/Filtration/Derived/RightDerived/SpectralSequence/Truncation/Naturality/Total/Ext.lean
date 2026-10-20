module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Truncation.Naturality.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensionality for total truncation-filtration realizations

This leaf complements the owner-level map extensionality with the canonical dependent object
extensionality inherited from the displayed total category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Two total truncation realizations are equal after identifying their bases and displayed objects. -/
@[ext (iff := false), stacks 0BKM "extensionality of total truncation realizations"]
theorem ext {S T : Realization.Total F}
    (h_base : S.base = T.base)
    (h_obj : DisplayedCategory.Obj.cast
      (displayedCategory F) h_base S.obj = T.obj) :
    S = T := sorry

/-- With a chosen equality of bases, equality of total truncation realizations is equivalent to
equality of their displayed objects after canonical transport. -/
@[simp, stacks 0BKM "equality criterion for total truncation realizations"]
theorem ext_iff_of_base {S T : Realization.Total F}
    (h_base : S.base = T.base) :
    S = T ↔ DisplayedCategory.Obj.cast
      (displayedCategory F) h_base S.obj = T.obj := sorry

/-- With a chosen equality of base maps, equality of total truncation maps is equivalent to
equality of their displayed maps after owner-level reindexing. -/
@[simp, stacks 0BKM "equality criterion for total truncation realization maps"]
theorem Hom.ext_reindex_iff {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base) :
    m = n ↔ Realization.Map.reindex F h_base m.displayed = n.displayed := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Truncation.Realization.Total
