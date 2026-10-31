/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSiteTensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Annihilator subobjects on commutative ringed sites

The annihilator of a module sheaf is the kernel of the scalar-action map from the structure
module to its internal endomorphism object.  This owner is independent of points, opens, and
ringed-space presentations; those layers add only section and stalk bridges.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.Annihilator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose
  (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- The scalar-action map from the structure module to the internal endomorphism sheaf, obtained
from the section of local identity endomorphisms. -/
@[stacks 0H2H "canonical action map"]
noncomputable def action (F : ringedSiteModuleCategory J O) :
    unitModule J O ⟶ (ihom F).obj F :=
  (InternalHom.obj O F F).unitHomEquiv.symm
    (InternalHom.homToSections O (𝟙 F))

/-- The action map sends a local scalar to multiplication by that scalar on the slice. -/
@[simp]
theorem action_val_app_apply (F : ringedSiteModuleCategory J O) (U : Cᵒᵖ)
    (r : O.obj.obj U) :
    ((action F).val.app U).hom r = SheafOfModules.sectionActionHom O F U.unop r := by
  change (SheafOfModules.overFunctor (ringSheaf J O) U.unop).map (𝟙 F) ≫
    SheafOfModules.sectionActionHom O F U.unop r = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The annihilator of a module sheaf as a kernel subobject of the structure module. -/
@[stacks 0H2H "annihilator subobject"]
noncomputable abbrev subobject (F : ringedSiteModuleCategory J O) :
    Subobject (unitModule J O) :=
  kernelSubobject (action F)

/-- The module sheaf underlying the annihilator subobject. -/
@[stacks 0H2H "annihilator module sheaf"]
noncomputable abbrev sheaf (F : ringedSiteModuleCategory J O) :
    ringedSiteModuleCategory J O :=
  subobject F

/-- The canonical inclusion of the annihilator into the structure module. -/
@[stacks 0H2H "annihilator inclusion"]
noncomputable abbrev ι (F : ringedSiteModuleCategory J O) :
    sheaf F ⟶ unitModule J O :=
  (subobject F).arrow

/-- The annihilator inclusion followed by the scalar-action map is zero. -/
@[reassoc, stacks 0H2H "annihilator kernel equation"]
theorem ι_comp_action (F : ringedSiteModuleCategory J O) :
    ι F ≫ action F = 0 := by
  exact kernelSubobject_arrow_comp (action F)

/-- An annihilator section also annihilates any isomorphic module sheaf. -/
theorem ι_comp_action_of_iso
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    ι F ≫ action G = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  let r := ((ι F).val.app U).hom s
  have hs := congrArg
    (fun f : sheaf F ⟶ (ihom F).obj F => (f.val.app U).hom s) (ι_comp_action F)
  change ((action F).val.app U).hom r = 0 at hs
  rw [action_val_app_apply] at hs
  change SheafOfModules.sectionActionHom O F U.unop r =
    (0 : F.over U.unop ⟶ F.over U.unop) at hs
  change ((action G).val.app U).hom r = 0
  rw [action_val_app_apply]
  change SheafOfModules.sectionActionHom O G U.unop r =
    (0 : G.over U.unop ⟶ G.over U.unop)
  have hi : e.inv.over U.unop ≫ e.hom.over U.unop = 𝟙 (G.over U.unop) :=
    ((SheafOfModules.overFunctor (ringSheaf J O) U.unop).mapIso e).inv_hom_id
  calc
    SheafOfModules.sectionActionHom O G U.unop r =
        (e.inv.over U.unop ≫ e.hom.over U.unop) ≫
          SheafOfModules.sectionActionHom O G U.unop r := by
      rw [hi, Category.id_comp]
    _ = e.inv.over U.unop ≫ SheafOfModules.sectionActionHom O F U.unop r ≫
        e.hom.over U.unop := by
      rw [Category.assoc, ← SheafOfModules.sectionActionHom_naturality O e.hom U.unop r]
    _ = 0 := by rw [hs, zero_comp, comp_zero]

/-- A morphism into the structure module factors through the annihilator exactly when it acts
trivially on `F`. -/
@[stacks 0H2H "annihilator universal property"]
theorem factors_iff (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O) :
    (subobject F).Factors f ↔ f ≫ action F = 0 := by
  exact kernelSubobject_factors_iff (action F) f

/-- The canonical lift of a morphism annihilated by the scalar action to the annihilator. -/
@[stacks 0H2H "annihilator lift"]
noncomputable def lift (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O)
    (h : f ≫ action F = 0) : K ⟶ sheaf F :=
  kernel.lift (action F) f h ≫ (kernelSubobjectIso (action F)).inv

/-- The annihilator lift followed by its inclusion recovers the original morphism. -/
@[reassoc, stacks 0H2H "annihilator lift equation"]
theorem lift_ι (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O)
    (h : f ≫ action F = 0) : lift F f h ≫ ι F = f := by
  change (kernel.lift (action F) f h ≫ (kernelSubobjectIso (action F)).inv) ≫
    (kernelSubobject (action F)).arrow = f
  rw [Category.assoc, kernelSubobject_arrow', kernel.lift_ι]

/-- Morphisms into the annihilator are determined by their composites with its inclusion. -/
@[ext, stacks 0H2H "annihilator morphism extensionality"]
theorem hom_ext (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} {f g : K ⟶ sheaf F}
    (h : f ≫ ι F = g ≫ ι F) : f = g := by
  exact (cancel_mono (subobject F).arrow).mp h

/-- Isomorphic module sheaves have the same annihilator subobject of the structure module. -/
@[stacks 0H2H "annihilator invariance under module isomorphism"]
theorem subobject_eq_of_iso
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    subobject F = subobject G := by
  apply le_antisymm
  · exact le_kernelSubobject (action G) (subobject F) (ι_comp_action_of_iso e)
  · exact le_kernelSubobject (action F) (subobject G) (ι_comp_action_of_iso e.symm)

/-- The isomorphism of annihilator module sheaves obtained by lifting their canonical inclusions
in both directions. -/
@[stacks 0H2H "annihilator isomorphism"]
noncomputable def mapIso
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    sheaf F ≅ sheaf G where
  hom := lift G (ι F) (ι_comp_action_of_iso e)
  inv := lift F (ι G) (ι_comp_action_of_iso e.symm)
  hom_inv_id := by
    apply hom_ext F
    simp only [Category.assoc, lift_ι, Category.id_comp]
  inv_hom_id := by
    apply hom_ext G
    simp only [Category.assoc, lift_ι, Category.id_comp]

/-- The annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "annihilator isomorphism inclusion"]
theorem mapIso_hom_ι
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    (mapIso e).hom ≫ ι G = ι F := by
  exact lift_ι G (ι F) (ι_comp_action_of_iso e)

/-- The inverse annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "inverse annihilator isomorphism inclusion"]
theorem mapIso_inv_ι
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    (mapIso e).inv ≫ ι F = ι G := by
  exact lift_ι F (ι G) (ι_comp_action_of_iso e.symm)

/-- The identity module isomorphism induces the identity annihilator isomorphism. -/
@[simp, stacks 0H2H "annihilator identity isomorphism"]
theorem mapIso_refl (F : ringedSiteModuleCategory J O) :
    mapIso (Iso.refl F) = Iso.refl (sheaf F) := by
  apply Iso.ext
  apply hom_ext F
  simpa only [Iso.refl_hom, Category.id_comp] using mapIso_hom_ι (Iso.refl F)

/-- Annihilator isomorphisms respect composition of module-sheaf isomorphisms. -/
@[simp, stacks 0H2H "annihilator composition isomorphism"]
theorem mapIso_trans
    {F G H : ringedSiteModuleCategory J O} (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := by
  apply Iso.ext
  apply hom_ext H
  simp only [Iso.trans_hom, Category.assoc, mapIso_hom_ι]

end SheafOfModules.RingedSite.Annihilator
