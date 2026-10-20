/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior algebras and restriction to a slice category

The sectionwise exterior-algebra presheaf commutes with precomposition by the forgetful functor
from a slice.  The comparison is not definitionally the identity: module-presheaf pushforward
retains a restriction of scalars along the identity ring morphism.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules.ExteriorAlgebra

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C)

/-- The objectwise comparison between restricting a sectionwise exterior algebra and taking
the exterior algebra after restriction. -/
noncomputable def overAppIso
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) (X : (Over U)ᵒᵖ) :
    ((presheaf O F).over U).obj X ≅
      (presheaf ((Over.forget U).op ⋙ O) (F.over U)).obj X :=
  Restriction.overAppIso (RingPresheaf O) U (presheaf O F) X ≪≫
    (ModuleCat.exteriorAlgebra.functor (O.obj ((Over.forget U).op.obj X))).mapIso
      (Restriction.overAppIso (RingPresheaf O) U F X).symm

/-- The objectwise exterior-algebra comparisons commute with restriction maps in the slice. -/
theorem overAppIso_naturality
    (F : PresheafOfModules.{max w z} (RingPresheaf O))
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((presheaf O F).over U).map f ≫
        (ModuleCat.restrictScalars
          ((((Over.forget U).op ⋙ O).map f).hom)).map (overAppIso O U F Y).hom =
      (overAppIso O U F X).hom ≫
        (presheaf ((Over.forget U).op ⋙ O) (F.over U)).map f := sorry

/-- Restriction to a slice commutes with the sectionwise exterior-algebra presheaf. -/
@[stacks 01CF "sectionwise exterior algebra and slice restriction"]
noncomputable def overIso
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (presheaf O F).over U ≅
      presheaf ((Over.forget U).op ⋙ O) (F.over U) :=
  PresheafOfModules.isoMk (overAppIso O U F)
    (fun _ _ f ↦ overAppIso_naturality O U F f)

/-- The slice comparison preserves the degree-one exterior-algebra generator. -/
theorem overIso_hom_ι
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (Hom.over (ι O F) U) ≫ (overIso O U F).hom =
      ι ((Over.forget U).op ⋙ O) (F.over U) := sorry

/-- The slice comparison is natural in the module presheaf. -/
theorem overIso_naturality
    {F G : PresheafOfModules.{max w z} (RingPresheaf O)} (f : F ⟶ G) :
    (functor O ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U).map f ≫
        (overIso O U G).hom =
      (overIso O U F).hom ≫
        (PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
          functor ((Over.forget U).op ⋙ O)).map f := sorry

/-- The inverse slice comparison is natural in the module presheaf. -/
@[stacks 01CF "inverse naturality of the exterior-algebra slice comparison"]
theorem overIso_inv_naturality
    {F G : PresheafOfModules.{max w z} (RingPresheaf O)} (f : F ⟶ G) :
    (PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
          functor ((Over.forget U).op ⋙ O)).map f ≫
        (overIso O U G).inv =
      (overIso O U F).inv ≫
        (functor O ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U).map f := sorry

/-- The forward exterior-algebra slice comparisons form a natural transformation. -/
@[stacks 01CF "forward exterior-algebra slice comparison natural transformation"]
noncomputable def overNatTrans :
    functor O ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U ⟶
      PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) where
  app F := (overIso O U F).hom
  naturality _ _ f := overIso_naturality O U f

/-- The inverse exterior-algebra slice comparisons form the inverse natural transformation. -/
@[stacks 01CF "inverse exterior-algebra slice comparison natural transformation"]
noncomputable def overInvNatTrans :
    PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) ⟶
      functor O ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U where
  app F := (overIso O U F).inv
  naturality _ _ f := overIso_inv_naturality O U f

/-- A component of the forward exterior-algebra slice comparison is `overIso`. -/
@[simp, stacks 01CF "forward exterior-algebra slice comparison component"]
theorem overNatTrans_app
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatTrans O U).app F = (overIso O U F).hom := sorry

/-- A component of the inverse exterior-algebra slice comparison is the inverse of `overIso`. -/
@[simp, stacks 01CF "inverse exterior-algebra slice comparison component"]
theorem overInvNatTrans_app
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overInvNatTrans O U).app F = (overIso O U F).inv := sorry

/-- The forward exterior-algebra slice comparison followed by its inverse is the identity. -/
@[simp, stacks 01CF "exterior-algebra slice comparison forward-inverse law"]
theorem overNatTrans_hom_inv_id :
    overNatTrans O U ≫ overInvNatTrans O U = 𝟙 _ := sorry

/-- The inverse exterior-algebra slice comparison followed by its forward map is the identity. -/
@[simp, stacks 01CF "exterior-algebra slice comparison inverse-forward law"]
theorem overNatTrans_inv_hom_id :
    overInvNatTrans O U ≫ overNatTrans O U = 𝟙 _ := sorry

/-- Restriction to a slice commutes naturally with the sectionwise exterior-algebra functor. -/
@[stacks 01CF "natural sectionwise exterior-algebra slice comparison"]
noncomputable def overNatIso :
    functor O ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U ≅
      PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) :=
  { hom := overNatTrans O U
    inv := overInvNatTrans O U
    hom_inv_id := overNatTrans_hom_inv_id O U
    inv_hom_id := overNatTrans_inv_hom_id O U }

/-- The forward natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra slice comparison natural isomorphism hom"]
theorem overNatIso_hom :
    (overNatIso O U).hom = overNatTrans O U := sorry

/-- The inverse natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CF "exterior-algebra slice comparison natural isomorphism inverse"]
theorem overNatIso_inv :
    (overNatIso O U).inv = overInvNatTrans O U := sorry

/-- A component of `overNatIso` is the objectwise exterior-algebra slice comparison. -/
@[simp, stacks 01CF "exterior-algebra slice comparison natural isomorphism component"]
theorem overNatIso_app
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U).app F = overIso O U F := sorry

/-- The forward component of `overNatIso` is the objectwise comparison map. -/
@[simp, stacks 01CF "exterior-algebra slice comparison natural isomorphism hom component"]
theorem overNatIso_hom_app
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U).hom.app F = (overIso O U F).hom := sorry

/-- The inverse component of `overNatIso` is the objectwise inverse comparison map. -/
@[simp, stacks 01CF "exterior-algebra slice comparison natural isomorphism inverse component"]
theorem overNatIso_inv_app
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U).inv.app F = (overIso O U F).inv := sorry

end PresheafOfModules.ExteriorAlgebra
