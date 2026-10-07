module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.Ring

/-!
# Normality under filtered colimits

The primary owner is the cocone-level theorem: it applies to any chosen
filtered-colimit presentation rather than only Mathlib's canonical colimit
object.  The under-category bridge is a thin categorical view of that result,
which prevents algebraic applications from rebuilding forgetful-functor
preservation arguments.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace IsNormalRing

variable {J : Type v} [SmallCategory J] [IsFiltered J]

/-- Lemma 10.37.17 (Stacks tag `037D`): a filtered colimit of normal
commutative rings is normal. -/
@[stacks 037D]
theorem of_isColimit_filtered
    (F : J ⥤ CommRingCat.{max u v}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, IsNormalRing (F.obj j)) :
    IsNormalRing c.pt := sorry

/-- A filtered colimit in the category of commutative rings under a fixed base
is normal when every underlying ring at a stage is normal. -/
theorem of_isColimit_under_filtered
    {A : CommRingCat.{u}} (F : J ⥤ CategoryTheory.Under A)
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, IsNormalRing (F.obj j)) :
    IsNormalRing c.pt := sorry

end IsNormalRing
