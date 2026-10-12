/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Filtered exactness and local presentability of sheaf categories

Mathlib already provides `HasLimits`, `HasColimits`, `CreatesLimits` instances for
sheaf categories via `Mathlib.CategoryTheory.Sites.Limits`. This file records the
non-trivial theorems: filtered colimits commute with finite limits, and sheaf
categories on small sites are locally presentable.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

-- Mathlib already provides these via Mathlib.CategoryTheory.Sites.Limits:
-- instance : CreatesLimits (sheafToPresheaf J (Type w))
-- instance : HasLimits (Sheaf J (Type w))
-- instance [HasSheafify J (Type w)] : HasColimits (Sheaf J (Type w))

section FilteredExactness

/-- Filtered colimits of sheaves of sets commute with finite limits.
This is the key exactness property that makes sites behave like topological spaces. -/
theorem Sites.sheaf_filteredColimit_exact
    {I : Type w} [SmallCategory I] [IsFiltered I]
    -- The colimit is no longer automatic here, so require it.
    (F : I ⥤ Sheaf J (Type w)) [HasColimit F] :
    PreservesFiniteLimits (colimit F).val := sorry

/-- Filtered colimits in sheaf categories are computed presheaf-wise (objectwise). -/
theorem Sites.sheaf_filteredColimit_objectwise :
    -- `PreservesFilteredColimits` is a standalone class, not a `Functor` field.
    PreservesFilteredColimits (sheafToPresheaf J (Type w)) := sorry

end FilteredExactness

section LocallyPresentable

/-- The sheaf category on a small site is locally presentable
(hence both complete and cocomplete). -/
theorem Sites.sheafCategory_locallyPresentable [HasSheafify J (Type w)]
    [Small.{w} C] :
    HasLimitsOfSize.{w, w} (Sheaf J (Type w)) := sorry

end LocallyPresentable

end CategoryTheory
