/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

open CategoryTheory
open AlgebraicGeometry

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- Every set-valued sheaf on a small fully faithful dense subsite of the étale site of a
field spectrum is represented by the restriction of an ambient étale scheme's Yoneda presheaf. -/
theorem sheaf_isRepresentableByEtaleScheme
    {C : Type u} [Category.{u} C] (K : Type u) [Field K]
    (J : GrothendieckTopology C) (ι : C ⥤ (Spec (.of K)).Etale)
    [ι.Full] [ι.Faithful] [ι.IsDenseSubsite J (Spec (.of K)).smallEtaleTopology]
    (F : Sheaf J (Type u)) :
    ∃ X : (Spec (.of K)).Etale, Nonempty (F.obj ≅ (ι.op ⋙ CategoryTheory.yoneda.obj X)) :=
  sorry

/-- A small fully faithful dense subsite of the étale site of a field spectrum has a
set-valued sheaf that is not represented by any object of that subsite. -/
theorem exists_not_isRepresentable_on_smallSite
    {C : Type u} [Category.{u} C] (K : Type u) [Field K]
    (J : GrothendieckTopology C) (ι : C ⥤ (Spec (.of K)).Etale)
    [ι.Full] [ι.Faithful] [ι.IsDenseSubsite J (Spec (.of K)).smallEtaleTopology] :
    ∃ F : Sheaf J (Type u), ¬ F.obj.IsRepresentable :=
  sorry

end AlgebraicGeometry.Scheme.Etale
