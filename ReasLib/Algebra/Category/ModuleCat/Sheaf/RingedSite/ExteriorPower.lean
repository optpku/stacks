/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exterior powers of module sheaves on ringed sites

This file sheafifies the sectionwise exterior-power functor over an arbitrary commutative ringed
site.  Ringed spaces and schemes are thin specializations of this topology-independent owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.ExteriorPower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The sectionwise degree-`n` exterior-power presheaf underlying a module sheaf. -/
@[stacks 01CG "sectionwise exterior power on a ringed site"]
noncomputable abbrev presheaf
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    PresheafOfModules (ringSheaf J 𝒪).obj :=
  PresheafOfModules.ExteriorPower.presheaf 𝒪.obj F.val n

/-- Evaluation of the sectionwise exterior-power presheaf at an object of the site. -/
@[simp, stacks 01CG "objectwise exterior power on a ringed site"]
theorem presheaf_obj
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) (U : Cᵒᵖ) :
    (presheaf 𝒪 F n).obj U =
      PresheafOfModules.ExteriorPower.obj 𝒪.obj F.val n U := sorry

/-- The morphism of sectionwise exterior-power presheaves induced by a module-sheaf morphism. -/
@[stacks 01CG "map on sectionwise exterior powers on a ringed site"]
noncomputable abbrev presheafMap
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    presheaf 𝒪 F n ⟶ presheaf 𝒪 G n :=
  PresheafOfModules.ExteriorPower.hom 𝒪.obj f.val n

/-- The degree-`n` exterior-power functor on module sheaves over a commutative ringed site. -/
@[stacks 01CG "exterior-power functor on a ringed site"]
noncomputable def functor (n : ℕ) :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.forget (ringSheaf J 𝒪) ⋙
    PresheafOfModules.ExteriorPower.functor 𝒪.obj n ⋙
    moduleSheafification 𝒪

/-- The degree-`n` exterior-power module sheaf on a commutative ringed site. -/
@[stacks 01CG "exterior power on a ringed site"]
noncomputable abbrev sheaf
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) : ringedSiteModuleCategory J 𝒪 :=
  (functor 𝒪 n).obj F

/-- The degree-`n` exterior-power sheaf is the sheafification of the sectionwise exterior-power
presheaf. -/
@[stacks 01CG "exterior power as a sheafification on a ringed site"]
theorem sheaf_eq_sheafification
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    sheaf 𝒪 F n =
      (moduleSheafification 𝒪).obj (presheaf 𝒪 F n) := sorry

/-- The canonical definitional isomorphism from the sheafification model to the exterior-power
sheaf. -/
@[stacks 01CG "canonical exterior-power sheafification isomorphism"]
noncomputable def sheafificationIso
    (F : ringedSiteModuleCategory J 𝒪) (n : ℕ) :
    (moduleSheafification 𝒪).obj (presheaf 𝒪 F n) ≅ sheaf 𝒪 F n :=
  Iso.refl _

/-- The morphism on degree-`n` exterior-power sheaves induced by a module-sheaf morphism. -/
@[stacks 01CG "map on exterior powers on a ringed site"]
noncomputable abbrev map
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    sheaf 𝒪 F n ⟶ sheaf 𝒪 G n :=
  (functor 𝒪 n).map f

/-- The isomorphism on degree-`n` exterior-power sheaves induced by an isomorphism of module
sheaves. -/
@[stacks 01CG "exterior power of a module-sheaf isomorphism"]
noncomputable def mapIso
    {F G : ringedSiteModuleCategory J 𝒪} (e : F ≅ G) (n : ℕ) :
    sheaf 𝒪 F n ≅ sheaf 𝒪 G n :=
  (functor 𝒪 n).mapIso e

/-- On underlying presheaves, the exterior-power sheaf map is the sheafification of the
sectionwise exterior-power map. -/
@[stacks 01CG "exterior-power map as a sheafification"]
theorem map_eq_sheafification
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) (n : ℕ) :
    map 𝒪 f n = (moduleSheafification 𝒪).map (presheafMap 𝒪 f n) := sorry

end SheafOfModules.RingedSite.ExteriorPower
