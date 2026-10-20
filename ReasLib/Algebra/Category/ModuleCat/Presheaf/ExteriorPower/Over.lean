/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior powers and restriction to a slice category

The degreewise sectionwise exterior-power presheaf commutes with restriction to a slice.  The
comparison explicitly removes the identity scalar restriction inserted by module-presheaf
pushforward and then applies functoriality of exterior powers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace PresheafOfModules.ExteriorPower

variable {C : Type u} [Category.{v} C]
variable (O : Cᵒᵖ ⥤ CommRingCat.{w}) (U : C)

/-- The objectwise comparison between restricting a sectionwise exterior power and taking the
exterior power after restriction. -/
noncomputable def overAppIso
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) (n : ℕ) (X : (Over U)ᵒᵖ) :
    ((presheaf O F n).over U).obj X ≅
      (presheaf ((Over.forget U).op ⋙ O) (F.over U) n).obj X :=
  Restriction.overAppIso (RingPresheaf O) U (presheaf O F n) X ≪≫
    (ModuleCat.exteriorPower.functor (O.obj ((Over.forget U).op.obj X)) n).mapIso
      (Restriction.overAppIso (RingPresheaf O) U F X).symm

/-- The objectwise exterior-power comparisons commute with restriction maps in the slice. -/
theorem overAppIso_naturality
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) (n : ℕ)
    {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y) :
    ((presheaf O F n).over U).map f ≫
        (ModuleCat.restrictScalars
          ((((Over.forget U).op ⋙ O).map f).hom)).map (overAppIso O U F n Y).hom =
      (overAppIso O U F n X).hom ≫
        (presheaf ((Over.forget U).op ⋙ O) (F.over U) n).map f := sorry

/-- Restriction to a slice commutes with the degree-`n` sectionwise exterior-power presheaf. -/
@[stacks 01CG "sectionwise exterior power and slice restriction"]
noncomputable def overIso
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) (n : ℕ) :
    (presheaf O F n).over U ≅
      presheaf ((Over.forget U).op ⋙ O) (F.over U) n :=
  PresheafOfModules.isoMk (overAppIso O U F n)
    (fun _ _ f ↦ overAppIso_naturality O U F n f)

/-- The slice comparison acts entrywise on exterior-power generators. -/
theorem overAppIso_hom_mk
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) (n : ℕ)
    (X : (Over U)ᵒᵖ) (m : Fin n → (F.over U).obj X) :
    (overAppIso O U F n X).hom
        (ModuleCat.exteriorPower.mk
          (R := O.obj ((Over.forget U).op.obj X))
          (M := F.obj ((Over.forget U).op.obj X)) m) =
      ModuleCat.exteriorPower.mk
        (R := ((Over.forget U).op ⋙ O).obj X) (M := (F.over U).obj X) m := sorry

set_option maxHeartbeats 400000 in
/-- The slice comparison is natural in the module presheaf. -/
theorem overIso_naturality
    (n : ℕ) {F G : PresheafOfModules.{max w z} (RingPresheaf O)} (f : F ⟶ G) :
    (functor O n ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U).map f ≫
        (overIso O U G n).hom =
      (overIso O U F n).hom ≫
        (PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
          functor ((Over.forget U).op ⋙ O) n).map f := sorry

set_option maxHeartbeats 400000 in
/-- The inverse degree-`n` slice comparison is natural in the module presheaf. -/
@[stacks 01CG "inverse naturality of the exterior-power slice comparison"]
theorem overIso_inv_naturality
    (n : ℕ) {F G : PresheafOfModules.{max w z} (RingPresheaf O)} (f : F ⟶ G) :
    (PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
          functor ((Over.forget U).op ⋙ O) n).map f ≫
        (overIso O U G n).inv =
      (overIso O U F n).inv ≫
        (functor O n ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U).map f := sorry

set_option maxHeartbeats 400000 in
/-- The forward degree-`n` slice comparisons form a natural transformation. -/
@[stacks 01CG "forward exterior-power slice comparison natural transformation"]
noncomputable def overNatTrans (n : ℕ) :
    functor O n ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U ⟶
      PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) n where
  app F := (overIso O U F n).hom
  naturality _ _ f := overIso_naturality O U n f

set_option maxHeartbeats 400000 in
/-- The inverse degree-`n` slice comparisons form the inverse natural transformation. -/
@[stacks 01CG "inverse exterior-power slice comparison natural transformation"]
noncomputable def overInvNatTrans (n : ℕ) :
    PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) n ⟶
      functor O n ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U where
  app F := (overIso O U F n).inv
  naturality _ _ f := overIso_inv_naturality O U n f

/-- A component of the forward degree-`n` slice comparison is `overIso`. -/
@[simp, stacks 01CG "forward exterior-power slice comparison component"]
theorem overNatTrans_app (n : ℕ)
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatTrans O U n).app F = (overIso O U F n).hom := sorry

/-- A component of the inverse degree-`n` slice comparison is the inverse of `overIso`. -/
@[simp, stacks 01CG "inverse exterior-power slice comparison component"]
theorem overInvNatTrans_app (n : ℕ)
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overInvNatTrans O U n).app F = (overIso O U F n).inv := sorry

/-- The forward degree-`n` slice comparison followed by its inverse is the identity. -/
@[simp, stacks 01CG "exterior-power slice comparison forward-inverse law"]
theorem overNatTrans_hom_inv_id (n : ℕ) :
    overNatTrans O U n ≫ overInvNatTrans O U n = 𝟙 _ := sorry

/-- The inverse degree-`n` slice comparison followed by its forward map is the identity. -/
@[simp, stacks 01CG "exterior-power slice comparison inverse-forward law"]
theorem overNatTrans_inv_hom_id (n : ℕ) :
    overInvNatTrans O U n ≫ overNatTrans O U n = 𝟙 _ := sorry

set_option maxHeartbeats 400000 in
/-- Restriction to a slice commutes naturally with the degree-`n` sectionwise exterior-power
functor. -/
@[stacks 01CG "natural sectionwise exterior-power slice comparison"]
noncomputable def overNatIso (n : ℕ) :
    functor O n ⋙ PresheafOfModules.overFunctor (RingPresheaf O) U ≅
      PresheafOfModules.overFunctor (RingPresheaf O) U ⋙
        functor ((Over.forget U).op ⋙ O) n :=
  { hom := overNatTrans O U n
    inv := overInvNatTrans O U n
    hom_inv_id := overNatTrans_hom_inv_id O U n
    inv_hom_id := overNatTrans_inv_hom_id O U n }

/-- The forward natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CG "exterior-power slice comparison natural isomorphism hom"]
theorem overNatIso_hom (n : ℕ) :
    (overNatIso O U n).hom = overNatTrans O U n := sorry

/-- The inverse natural transformation of `overNatIso` is explicit. -/
@[simp, stacks 01CG "exterior-power slice comparison natural isomorphism inverse"]
theorem overNatIso_inv (n : ℕ) :
    (overNatIso O U n).inv = overInvNatTrans O U n := sorry

/-- A component of `overNatIso` is the objectwise degree-`n` slice comparison. -/
@[simp, stacks 01CG "exterior-power slice comparison natural isomorphism component"]
theorem overNatIso_app (n : ℕ)
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U n).app F = overIso O U F n := sorry

/-- The forward component of `overNatIso` is the objectwise comparison map. -/
@[simp, stacks 01CG "exterior-power slice comparison natural isomorphism hom component"]
theorem overNatIso_hom_app (n : ℕ)
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U n).hom.app F = (overIso O U F n).hom := sorry

/-- The inverse component of `overNatIso` is the objectwise inverse comparison map. -/
@[simp, stacks 01CG "exterior-power slice comparison natural isomorphism inverse component"]
theorem overNatIso_inv_app (n : ℕ)
    (F : PresheafOfModules.{max w z} (RingPresheaf O)) :
    (overNatIso O U n).inv.app F = (overIso O U F n).inv := sorry

end PresheafOfModules.ExteriorPower
