/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import ReasLib.CategoryTheory.Sites.TopCat.Sheafification
public import ReasLib.CategoryTheory.Sites.TopCat.Size
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/- Remark 87.2.4 (Sheafification of presheaves of topological spaces)
Sheafification is the left adjoint of the inclusion of sheaves of topological spaces
into presheaves. -/
@[stacks 0AI4] #check
  (CategoryTheory.hasWeakSheafify_topCat J : HasWeakSheafify J TopCat.{max u v})

section limits

variable {I : Type (max u v)} [Category.{max u v} I]
variable (D : I ⥤ Sheaf J TopCat.{max u v}) (U : C)

/- The category
of sheaves of topological spaces has limits, created and preserved by the inclusion into
presheaves, and computed objectwise in `TopCat`. -/
#check (inferInstance : HasLimits (Sheaf J TopCat.{max u v}))

#check
  (inferInstance : CreatesLimits (sheafToPresheaf J TopCat.{max u v}))

#check
  (inferInstance : PreservesLimits (sheafToPresheaf J TopCat.{max u v}))

#check
  ((CategoryTheory.preservesLimitIso
      (sheafToPresheaf J TopCat.{max u v}) D).app (op U) ≪≫
    CategoryTheory.Limits.limitObjIsoLimitCompEvaluation
      (D ⋙ sheafToPresheaf J TopCat.{max u v}) (op U) :
    (limit D).obj.obj (op U) ≅
      limit (D ⋙ sheafToPresheaf J TopCat.{max u v} ⋙
        (evaluation Cᵒᵖ TopCat.{max u v}).obj (op U)))

end limits

section imageSubsheaf

variable {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}}
variable (φ : F ⟶ G.obj)

/- Any map
`F ⟶ G` with `G` a sheaf of topological spaces factors through the image-generated
subsheaf, whose size is bounded by a cardinal depending only on `C` and `F`. -/
#check
  (CategoryTheory.Presheaf.topCatSize_def F :
    Presheaf.topCatSize F = ⨆ U : C, Cardinal.mk (F.obj (op U)))

#check
  (CategoryTheory.Presheaf.mem_imageGenerated_iff φ :
    ∀ {U : C} (s : G.obj.obj (op U)),
      (∃ t : (Presheaf.imageGenerated φ).obj.obj (op U),
          (Presheaf.imageGeneratedι φ).hom.app (op U) t = s) ↔
        ∃ R : J.Cover U, ∀ I : R.Arrow, ∃ t : F.obj (op I.Y),
          φ.app (op I.Y) t = G.obj.map I.f.op s)

#check
  (CategoryTheory.Presheaf.imageGenerated_factors φ :
    Presheaf.toImageGenerated φ ≫ (Presheaf.imageGeneratedι φ).hom = φ)

#check
  (CategoryTheory.Presheaf.exists_imageGenerated_size_bound J F :
    ∃ κ : Cardinal.{max u v},
      ∀ (G : Sheaf J TopCat.{max u v}) (φ : F ⟶ G.obj),
        Presheaf.topCatSize (Presheaf.imageGenerated φ).obj ≤ κ)

end imageSubsheaf

section adjunction

variable (F : Cᵒᵖ ⥤ TopCat.{max u v}) (G : Sheaf J TopCat.{max u v})

/- Sheafification
of presheaves of topological spaces is the left adjoint of the inclusion, with the
source Hom-formula as the adjunction equivalence. -/
#check
  ((CategoryTheory.sheafificationAdjunction J TopCat.{max u v}).homEquiv F G :
    ((presheafToSheaf J TopCat.{max u v}).obj F ⟶ G) ≃ (F ⟶ G.obj))

end adjunction

section stalks

variable (Φ : Point.{max u v} J) (M : TopCat.{max u v})

/- For a point
of the site, `U ↦ ∏_{x ∈ u(U)} M` with the product topology is a sheaf of topological
spaces, and sheafification commutes with taking stalks. -/
#check
  (CategoryTheory.GrothendieckTopology.Point.isSheaf_skyscraperPresheaf Φ M :
    Presheaf.IsSheaf J (Φ.skyscraperPresheaf M))

#check
  (CategoryTheory.GrothendieckTopology.Point.presheafToSheafCompSheafFiberIso
    Φ TopCat.{max u v} :
    presheafToSheaf J TopCat.{max u v} ⋙ Φ.sheafFiber ≅ Φ.presheafFiber)

end stalks
