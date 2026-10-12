/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import stacks_project.Chap87.Remark_87_2_4_Sheafification_of_presheaves_of_topological_spaces_ImageSubsheaf
public import stacks_project.Chap87.Remark_87_2_4_Sheafification_of_presheaves_of_topological_spaces_Instances
public import stacks_project.Chap87.Remark_87_2_4_Sheafification_of_presheaves_of_topological_spaces_Size
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

section limits

variable {I : Type (max u v)} [Category.{max u v} I]
variable (D : I ⥤ Sheaf J TopCat.{max u v}) (U : C)

/- Remark 87.2.4 (Sheafification of presheaves of topological spaces) (1): the category
of sheaves of topological spaces has limits, created and preserved by the inclusion into
presheaves, and computed objectwise in `TopCat`. -/
@[stacks 0AI4] #check (inferInstance : HasLimits (Sheaf J TopCat.{max u v}))

@[stacks 0AI4] #check
  (inferInstance : CreatesLimits (sheafToPresheaf J TopCat.{max u v}))

@[stacks 0AI4] #check
  (inferInstance : PreservesLimits (sheafToPresheaf J TopCat.{max u v}))

@[stacks 0AI4] #check
  ((preservesLimitIso (sheafToPresheaf J TopCat.{max u v}) D).app (op U) ≪≫
    limitObjIsoLimitCompEvaluation (D ⋙ sheafToPresheaf J TopCat.{max u v}) (op U) :
    (limit D).obj.obj (op U) ≅
      limit (D ⋙ sheafToPresheaf J TopCat.{max u v} ⋙
        (evaluation Cᵒᵖ TopCat.{max u v}).obj (op U)))

end limits

section imageSubsheaf

variable {F : Cᵒᵖ ⥤ TopCat.{max u v}} {G : Sheaf J TopCat.{max u v}}
variable (φ : F ⟶ G.obj)

/- Remark 87.2.4 (Sheafification of presheaves of topological spaces) (2): any map
`F ⟶ G` with `G` a sheaf of topological spaces factors through the image-generated
subsheaf, whose size is bounded by a cardinal depending only on `C` and `F`. -/
@[stacks 0AI4] #check
  (Presheaf.imageGenerated_factors φ :
    Presheaf.toImageGenerated φ ≫ (Presheaf.imageGeneratedι φ).hom = φ)

@[stacks 0AI4] #check
  (Presheaf.exists_imageGenerated_size_bound J F :
    ∃ κ : Cardinal.{max u v},
      ∀ (G : Sheaf J TopCat.{max u v}) (φ : F ⟶ G.obj),
        Presheaf.topCatSize (Presheaf.imageGenerated φ).obj ≤ κ)

end imageSubsheaf

section adjunction

variable (F : Cᵒᵖ ⥤ TopCat.{max u v}) (G : Sheaf J TopCat.{max u v})

/- Remark 87.2.4 (Sheafification of presheaves of topological spaces) (3): sheafification
of presheaves of topological spaces is the left adjoint of the inclusion, with the
source Hom-formula as the adjunction equivalence. -/
@[stacks 0AI4] #check (inferInstance : HasWeakSheafify J TopCat.{max u v})

@[stacks 0AI4] #check
  ((sheafificationAdjunction J TopCat.{max u v}).homEquiv F G :
    ((presheafToSheaf J TopCat.{max u v}).obj F ⟶ G) ≃ (F ⟶ G.obj))

end adjunction

section stalks

variable (Φ : Point.{max u v} J) (M : TopCat.{max u v})

/- Remark 87.2.4 (Sheafification of presheaves of topological spaces) (4): for a point
of the site, `U ↦ ∏_{x ∈ u(U)} M` with the product topology is a sheaf of topological
spaces, and sheafification commutes with taking stalks. -/
@[stacks 0AI4] #check
  (Φ.isSheaf_skyscraperPresheaf M : Presheaf.IsSheaf J (Φ.skyscraperPresheaf M))

@[stacks 0AI4] #check
  (Φ.presheafToSheafCompSheafFiberIso TopCat.{max u v} :
    presheafToSheaf J TopCat.{max u v} ⋙ Φ.sheafFiber ≅ Φ.presheafFiber)

end stalks
