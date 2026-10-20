module

public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Distinct representatives in filtered colimits of types

Mathlib characterizes equality of two stage representatives by equality after mapping them to a
common successor.  This leaf exposes the complementary inequality criteria, which are often the
most convenient API for proving that two elements of a filtered colimit remain distinct.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Limits.Types.FilteredColimit

variable {J : Type v} [Category.{w} J] [IsFiltered J]
variable {F : J ⥤ Type u} [HasColimit F]

/-- Two stage representatives determine different colimit elements exactly when their images
are different at every common successor. -/
theorem colimit_ι_ne_iff {i j : J} (x : F.obj i) (y : F.obj j) :
    colimit.ι F i x ≠ colimit.ι F j y ↔
      ∀ (k : J) (f : i ⟶ k) (g : j ⟶ k), F.map f x ≠ F.map g y := sorry

/-- For representatives from one stage, it suffices to test their images under each single
outgoing morphism. -/
theorem colimit_ι_ne_iff' {i : J} (x y : F.obj i) :
    colimit.ι F i x ≠ colimit.ι F i y ↔
      ∀ (j : J) (f : i ⟶ j), F.map f x ≠ F.map f y := sorry

end CategoryTheory.Limits.Types.FilteredColimit
