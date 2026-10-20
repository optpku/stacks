/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower.Monoid
public import ReasLib.CategoryTheory.GradedObject.Total.Monoidal
import Mathlib.Tactic.CrossRefAttribute

/-!
# The exterior algebra as a total monoid object

The total exterior algebra is the image of the graded exterior-power monoid under strong
monoidal totalization.  It is deliberately a `Mon`: ordinary commutativity would discard the
Koszul sign carried by the graded exterior algebra.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonObj

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (O : Sheaf J CommRingCat.{max u v})

/-- The exterior algebra functor valued in monoid objects of module sheaves, obtained by
totalizing the canonical graded exterior algebra. -/
@[stacks 01CF "total exterior-algebra monoid functor"]
noncomputable def monFunctor :
    ringedSiteModuleCategory J O ⥤ Mon (ringedSiteModuleCategory J O) :=
  ExteriorPower.monFunctor O ⋙
    (GradedObject.Total.functor
      (I := ℕ) (C := ringedSiteModuleCategory J O)).mapMon

/-- The underlying object of the total exterior monoid is the coproduct of its exterior-power
sheaves. -/
@[simp, stacks 01CF "underlying object of a total exterior algebra"]
theorem monFunctor_obj_X (F : ringedSiteModuleCategory J O) :
    ((monFunctor O).obj F).X =
      ∐ fun n : ℕ ↦ ExteriorPower.gradedObject O F n := sorry

/-- The unit of the total exterior monoid is the homogeneous degree-zero unit followed by the
coproduct inclusion. -/
@[stacks 01CF "unit of a total exterior algebra"]
theorem monFunctor_obj_one (F : ringedSiteModuleCategory J O) :
    η[((monFunctor O).obj F).X] =
      ExteriorPower.gradedOne O F ≫
        Limits.Sigma.ι (ExteriorPower.gradedObject O F) 0 := sorry

/-- On homogeneous summands, multiplication in the total exterior monoid is the fixed-degree
exterior product followed by inclusion into degree `n + m`. -/
@[reassoc (attr := simp), stacks 01CF "multiplication in a total exterior algebra"]
theorem sigmaι_tensor_sigmaι_mul
    (F : ringedSiteModuleCategory J O) (n m : ℕ) :
    (Limits.Sigma.ι (ExteriorPower.gradedObject O F) n ⊗ₘ
        Limits.Sigma.ι (ExteriorPower.gradedObject O F) m) ≫
        μ[((monFunctor O).obj F).X] =
      ExteriorPower.gradedMul O F n m ≫
        Limits.Sigma.ι (ExteriorPower.gradedObject O F) (n + m) := sorry

/-- Forgetting the total exterior-algebra multiplication gives the coproduct of the
exterior-power functor. -/
@[stacks 01CF "underlying module functor of the total exterior algebra"]
theorem monFunctor_comp_forget :
    monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) =
      ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O) := sorry

/-- The total of the exterior-power sheaves is canonically the underlying object of the total
exterior monoid. -/
noncomputable def totalMonAppIso (F : ringedSiteModuleCategory J O) :
    (ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O)).obj F ≅
      ((monFunctor O).obj F).X :=
  Iso.refl _

/-- The objectwise total exterior-monoid identifications are natural in the module sheaf. -/
theorem totalMonAppIso_hom_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (ExteriorPower.gradedObjectFunctor O ⋙
          GradedObject.Total.functor
            (I := ℕ) (C := ringedSiteModuleCategory J O)).map f ≫
        (totalMonAppIso O G).hom =
      (totalMonAppIso O F).hom ≫
        (monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O)).map f := sorry

/-- Naturality of the inverse objectwise total exterior-monoid identification. -/
@[stacks 01CF "inverse total exterior-monoid identification naturality"]
theorem totalMonAppIso_inv_naturality
    {F G : ringedSiteModuleCategory J O} (f : F ⟶ G) :
    (monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O)).map f ≫
        (totalMonAppIso O G).inv =
      (totalMonAppIso O F).inv ≫
        (ExteriorPower.gradedObjectFunctor O ⋙
          GradedObject.Total.functor
            (I := ℕ) (C := ringedSiteModuleCategory J O)).map f := sorry

/-- The forward natural transformation for total exterior-monoid underlying objects. -/
@[stacks 01CF "forward total exterior-monoid natural transformation"]
noncomputable def totalMonNatTrans :
    ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O) ⟶
      monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) where
  app F := (totalMonAppIso O F).hom
  naturality F G f := totalMonAppIso_hom_naturality O f

/-- The inverse natural transformation for total exterior-monoid underlying objects. -/
@[stacks 01CF "inverse total exterior-monoid natural transformation"]
noncomputable def totalMonInvNatTrans :
    monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) ⟶
      ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O) where
  app F := (totalMonAppIso O F).inv
  naturality F G f := totalMonAppIso_inv_naturality O f

/-- The forward total exterior-monoid transformation followed by its inverse is identity. -/
@[simp, stacks 01CF "total exterior-monoid natural transformation hom-inverse law"]
theorem totalMonNatTrans_hom_inv_id :
    totalMonNatTrans O ≫ totalMonInvNatTrans O =
      𝟙 (ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O)) := sorry

/-- The inverse total exterior-monoid transformation followed by its forward map is identity. -/
@[simp, stacks 01CF "total exterior-monoid natural transformation inverse-hom law"]
theorem totalMonNatTrans_inv_hom_id :
    totalMonInvNatTrans O ≫ totalMonNatTrans O =
      𝟙 (monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O)) := sorry

/-- The total exterior-power functor is naturally the underlying functor of the total exterior
monoid. -/
@[stacks 01CF "underlying functor of the total exterior monoid"]
noncomputable def totalMonIso :
    ExteriorPower.gradedObjectFunctor O ⋙
        GradedObject.Total.functor
          (I := ℕ) (C := ringedSiteModuleCategory J O) ≅
      monFunctor O ⋙ Mon.forget (ringedSiteModuleCategory J O) :=
  { hom := totalMonNatTrans O
    inv := totalMonInvNatTrans O
    hom_inv_id := totalMonNatTrans_hom_inv_id O
    inv_hom_id := totalMonNatTrans_inv_hom_id O }

/-- A component of `totalMonIso` is the canonical objectwise identification. -/
@[simp]
theorem totalMonIso_app (F : ringedSiteModuleCategory J O) :
    (totalMonIso O).app F = totalMonAppIso O F := sorry

end SheafOfModules.RingedSite.ExteriorAlgebra
