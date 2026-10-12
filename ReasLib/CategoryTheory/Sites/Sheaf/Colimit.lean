/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Colimits of sheaves

This leaf names the canonical presentation of a colimit of sheaves as the
sheafification of the colimit of the underlying presheaves.  It is independent
of filteredness, cardinality bounds, and any particular presentation of a
site.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w z wI vI

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [Category.{z} A]
variable {I : Type wI} [Category.{vI} I]
variable [HasWeakSheafify J A]

/-- The sheafification of the colimit of the underlying presheaf diagram is canonically
isomorphic to the chosen colimit of the sheaf diagram. -/
@[stacks 0GS0 "sheafified presheaf colimit"]
noncomputable def sheafifyColimitIso
    (F : I ⥤ Sheaf J A) [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J A)] :
    (presheafToSheaf J A).obj
        (colimit (F ⋙ sheafToPresheaf J A)) ≅ colimit F :=
  (colimit.isoColimitCocone
    ⟨Sheaf.sheafifyCocone (colimit.cocone (F ⋙ sheafToPresheaf J A)),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩).symm

/-- The canonical sheafified-colimit isomorphism identifies each sheafified
presheaf-colimit cocone leg with the chosen sheaf-colimit leg. -/
@[reassoc (attr := simp)]
theorem sheafifyColimitIso_ι_hom
    (F : I ⥤ Sheaf J A) [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J A)] (i : I) :
    (Sheaf.sheafifyCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J A))).ι.app i ≫
      (sheafifyColimitIso F).hom =
        colimit.ι F i := sorry

/-- The inverse sheafified-colimit isomorphism transports each chosen sheaf-colimit leg back
to the corresponding sheafified presheaf-colimit leg. -/
@[reassoc (attr := simp)]
theorem sheafifyColimitIso_ι_inv
    (F : I ⥤ Sheaf J A) [HasColimit F]
    [HasColimit (F ⋙ sheafToPresheaf J A)] (i : I) :
    colimit.ι F i ≫ (sheafifyColimitIso F).inv =
      (Sheaf.sheafifyCocone
        (colimit.cocone (F ⋙ sheafToPresheaf J A))).ι.app i := sorry

end CategoryTheory.Sheaf

end
