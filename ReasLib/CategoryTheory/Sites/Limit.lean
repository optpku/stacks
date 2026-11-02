/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Coherent.ExtensiveColimits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!
# Filtered exactness and local presentability of sheaf categories

Mathlib already provides `HasLimits`, `HasColimits`, `CreatesLimits` instances for
sheaf categories via `Mathlib.CategoryTheory.Sites.Limits`. This file records the
filtered exactness and the canonical sheafification description of colimits.
The historical local-presentability declaration below currently records only
completeness; the stronger API is an explicit follow-up.
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

The colimit functor itself is the functor that preserves finite limits.  In
particular, this statement does not say that the underlying presheaf of one
chosen colimit object is terminal or otherwise preserves a limit.  The
sheafification hypothesis supplies the colimits in the sheaf category and is
also the left-exactness input in the usual proof. -/
theorem Sites.sheaf_filteredColimit_exact
    {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasSheafify J (Type w)] :
    PreservesFiniteLimits (colim : (I ⥤ Sheaf J (Type w)) ⥤ Sheaf J (Type w)) := sorry

/-!
The following comparison is the general arbitrary-site replacement for an
objectwise colimit assertion.  A sheaf colimit is the sheafification of the
presheaf colimit; the isomorphism below is obtained from the two native
colimit universal properties, rather than from an assumed isomorphism.
-/
noncomputable def Sites.sheaf_filteredColimit_sheafificationComparison
    {I : Type w} [SmallCategory I]
    (F : I ⥤ Sheaf J (Type w))
    [HasWeakSheafify J (Type w)] [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J (Type w))] :
    (presheafToSheaf J (Type w)).obj
        (colimit (F ⋙ sheafToPresheaf J (Type w))) ≅ colimit F :=
  (Sheaf.isColimitSheafifyCocone
      (colimit.cocone (F ⋙ sheafToPresheaf J (Type w)))
      (colimit.isColimit (F ⋙ sheafToPresheaf J (Type w)))).coconePointUniqueUpToIso
    (colimit.isColimit F)

/-- Filtered colimits in sheaf categories are computed objectwise for the
finitary extensive topology.  This is deliberately a specialization: the
arbitrary-site interface is the sheafification comparison above, since the
infinite discrete finite-support example shows that unconditional objectwise
preservation is false. -/
theorem Sites.sheaf_filteredColimit_objectwise
    {C : Type u} [Category.{v} C] [FinitaryExtensive C]
    [HasSheafify (extensiveTopology C) (Type w)] :
    PreservesFilteredColimitsOfSize.{w, w}
      (sheafToPresheaf (extensiveTopology C) (Type w)) where
  preserves_filtered_colimits _ := inferInstance

end FilteredExactness

section LocallyPresentable

/-- The sheaf category on a small site is locally presentable
(hence both complete and cocomplete).  The current API conclusion only
asserts `HasLimitsOfSize`; a separate follow-up should provide the actual
local-presentability structure. -/
theorem Sites.sheafCategory_locallyPresentable [HasSheafify J (Type w)]
    [Small.{w} C] :
    HasLimitsOfSize.{w, w} (Sheaf J (Type w)) := sorry

end LocallyPresentable

end CategoryTheory
