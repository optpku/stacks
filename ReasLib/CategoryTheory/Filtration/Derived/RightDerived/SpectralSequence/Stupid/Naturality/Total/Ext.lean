/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Derived.RightDerived.SpectralSequence.Stupid.Naturality.Total
public import ReasLib.CategoryTheory.DisplayedCategory.Total.Transport
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extensionality for total stupid-filtration realizations

The displayed stupid map owner already provides reindexing across equal source maps.  This leaf
exposes that owner-level equality as the extensionality principle for the total category.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe wA wB vA vB uA uB

namespace CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
variable (F : A ⥤ B) [F.Additive] [F.PreservesMonomorphisms]
  [Functor.RightDerived.KInjective.HasDerived F] [HasInjectiveResolutions A]

/-- Two total stupid realizations are equal after identifying their bases and displayed objects. -/
@[ext (iff := false), stacks 0FLK "extensionality of total stupid realizations"]
theorem ext {S T : Realization.Total F}
    (h_base : S.base = T.base)
    (h_obj : DisplayedCategory.Obj.cast
      (displayedCategory F) h_base S.obj = T.obj) :
    S = T := sorry

/-- With a chosen equality of bases, equality of total stupid realizations is equivalent to
equality of their displayed objects after canonical transport. -/
@[simp, stacks 0FLK "equality criterion for total stupid realizations"]
theorem ext_iff_of_base {S T : Realization.Total F}
    (h_base : S.base = T.base) :
    S = T ↔ DisplayedCategory.Obj.cast
      (displayedCategory F) h_base S.obj = T.obj := sorry

/-- Two total stupid realization maps are equal after owner-level reindexing. -/
@[ext (iff := false), stacks 0FLK "extensionality of total stupid realization maps"]
theorem Hom.ext_reindex {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base)
    (h_map : Realization.Map.reindex F h_base m.displayed = n.displayed) :
    m = n := sorry

/-- With a chosen equality of base maps, equality of total stupid maps is equivalent to equality
of their displayed maps after owner-level reindexing. -/
@[simp, stacks 0FLK "equality criterion for total stupid realization maps"]
theorem Hom.ext_reindex_iff {S T : Realization.Total F} {m n : S ⟶ T}
    (h_base : m.base = n.base) :
    m = n ↔ Realization.Map.reindex F h_base m.displayed = n.displayed := sorry

end CategoryTheory.FilteredComplex.RightDerived.SpectralSequence.Stupid.Realization.Total
