/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Realization.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensionality for total unbounded right-derived realizations

The total category is dependent over the filtered-complex base.  These thin aliases expose the
canonical displayed-category extensionality under the realization namespace, so downstream code
does not need to mention the implementation-level displayed owner.
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

/-- Two total realization objects are equal after identifying their bases and displayed objects. -/
@[ext (iff := false), stacks 0BKK "extensionality of total right-derived realizations"]
theorem ext {S T : Realization.Total F}
    (h_base : S.base = T.base)
    (h_obj : DisplayedCategory.Obj.cast
      (SpectralSequence.displayedCategory F) h_base S.obj = T.obj) :
    S = T := sorry

/-- With a fixed base equality, total-object equality is equivalent to displayed-object equality. -/
@[simp, stacks 0BKK "base-relative extensionality of total right-derived realizations"]
theorem ext_iff_of_base {S T : Realization.Total F}
    (h_base : S.base = T.base) :
    S = T ↔ DisplayedCategory.Obj.cast
      (SpectralSequence.displayedCategory F) h_base S.obj = T.obj := sorry

/-- Two total realization maps are equal after identifying their base and displayed components. -/
@[ext (iff := false), stacks 0BKK "extensionality of total right-derived realization maps"]
theorem Hom.ext {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base)
    (h_displayed : DisplayedCategory.Hom.cast
      (SpectralSequence.displayedCategory F) h_base m.displayed = n.displayed) :
    m = n := sorry

/-- With a fixed base-map equality, total-map equality is equivalent to displayed-map equality. -/
@[simp, stacks 0BKK "base-relative extensionality of total right-derived realization maps"]
theorem Hom.ext_iff_of_base {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base) :
    m = n ↔ DisplayedCategory.Hom.cast
      (SpectralSequence.displayedCategory F) h_base m.displayed = n.displayed := sorry

/-- Two total realization maps are equal when their base maps agree and their displayed maps
agree after owner-level reindexing. -/
@[ext (iff := false), stacks 0BKK "owner-level extensionality of total realization maps"]
theorem Hom.ext_reindex {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base)
    (h_map : Realization.Map.reindex F h_base m.displayed = n.displayed) :
    m = n := sorry

/-- Equality of total realization maps is equivalent to equality of their displayed maps after
owner-level reindexing along a chosen base-map equality. -/
@[simp, stacks 0BKK "owner-level equality criterion for total realization maps"]
theorem Hom.ext_reindex_iff {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base) :
    m = n ↔ Realization.Map.reindex F h_base m.displayed = n.displayed := sorry

end Total

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Realization
