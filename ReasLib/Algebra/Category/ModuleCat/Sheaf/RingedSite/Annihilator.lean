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

/-- The scalar-action map from the structure module to the internal endomorphism sheaf of a
module sheaf. -/
@[stacks 0H2H "canonical action map"]
noncomputable def action (F : ringedSiteModuleCategory J O) :
    unitModule J O ⟶ (ihom F).obj F :=
  (unitIsoTensorUnit (J := J) (𝒪 := O)).hom ≫ MonoidalClosed.id F

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
    ι F ≫ action F = 0 := sorry

/-- A morphism into the structure module factors through the annihilator exactly when it acts
trivially on `F`. -/
@[stacks 0H2H "annihilator universal property"]
theorem factors_iff (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O) :
    (subobject F).Factors f ↔ f ≫ action F = 0 := sorry

/-- The canonical lift of a morphism annihilated by the scalar action to the annihilator. -/
@[stacks 0H2H "annihilator lift"]
noncomputable def lift (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O)
    (h : f ≫ action F = 0) : K ⟶ sheaf F :=
  factorThruKernelSubobject (action F) f h

/-- The annihilator lift followed by its inclusion recovers the original morphism. -/
@[reassoc, stacks 0H2H "annihilator lift equation"]
theorem lift_ι (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} (f : K ⟶ unitModule J O)
    (h : f ≫ action F = 0) : lift F f h ≫ ι F = f := sorry

/-- Morphisms into the annihilator are determined by their composites with its inclusion. -/
@[ext, stacks 0H2H "annihilator morphism extensionality"]
theorem hom_ext (F : ringedSiteModuleCategory J O)
    {K : ringedSiteModuleCategory J O} {f g : K ⟶ sheaf F}
    (h : f ≫ ι F = g ≫ ι F) : f = g := sorry

/-- Isomorphic module sheaves have the same annihilator subobject of the structure module. -/
@[stacks 0H2H "annihilator invariance under module isomorphism"]
theorem subobject_eq_of_iso
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    subobject F = subobject G := sorry

/-- The isomorphism of annihilator module sheaves induced by a module-sheaf isomorphism. -/
@[stacks 0H2H "annihilator isomorphism"]
noncomputable def mapIso
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    sheaf F ≅ sheaf G :=
  Subobject.isoOfEq (subobject F) (subobject G) (subobject_eq_of_iso e)

/-- The annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "annihilator isomorphism inclusion"]
theorem mapIso_hom_ι
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    (mapIso e).hom ≫ ι G = ι F := sorry

/-- The inverse annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "inverse annihilator isomorphism inclusion"]
theorem mapIso_inv_ι
    {F G : ringedSiteModuleCategory J O} (e : F ≅ G) :
    (mapIso e).inv ≫ ι F = ι G := sorry

/-- The identity module isomorphism induces the identity annihilator isomorphism. -/
@[simp, stacks 0H2H "annihilator identity isomorphism"]
theorem mapIso_refl (F : ringedSiteModuleCategory J O) :
    mapIso (Iso.refl F) = Iso.refl (sheaf F) := sorry

/-- Annihilator isomorphisms respect composition of module-sheaf isomorphisms. -/
@[simp, stacks 0H2H "annihilator composition isomorphism"]
theorem mapIso_trans
    {F G H : ringedSiteModuleCategory J O} (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := sorry

end SheafOfModules.RingedSite.Annihilator
