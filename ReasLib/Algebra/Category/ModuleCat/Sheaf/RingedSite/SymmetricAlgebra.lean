/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.SymmetricAlgebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric algebras of module sheaves on ringed sites

This file sheafifies the sectionwise symmetric-algebra functor over an arbitrary commutative
ringed site.  Ringed spaces and schemes only need thin specializations of this owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.SymmetricAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable (𝒪 : Sheaf J CommRingCat.{max u v})

/-- The sectionwise symmetric-algebra presheaf underlying a module sheaf. -/
noncomputable abbrev presheaf (F : ringedSiteModuleCategory J 𝒪) :
    PresheafOfModules (ringSheaf J 𝒪).obj :=
  PresheafOfModules.SymmetricAlgebra.presheaf 𝒪.obj F.val

/-- The morphism of sectionwise symmetric-algebra presheaves induced by a module-sheaf
morphism. -/
noncomputable abbrev presheafMap
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    presheaf 𝒪 F ⟶ presheaf 𝒪 G :=
  PresheafOfModules.SymmetricAlgebra.hom 𝒪.obj f.val

/-- The degree-one inclusion into the sectionwise symmetric-algebra presheaf. -/
noncomputable abbrev presheafι (F : ringedSiteModuleCategory J 𝒪) :
    F.val ⟶ presheaf 𝒪 F :=
  PresheafOfModules.SymmetricAlgebra.ι 𝒪.obj F.val

/-- The symmetric-algebra functor on module sheaves over a commutative ringed site. -/
noncomputable def functor :
    ringedSiteModuleCategory J 𝒪 ⥤ ringedSiteModuleCategory J 𝒪 :=
  SheafOfModules.forget (ringSheaf J 𝒪) ⋙
    PresheafOfModules.SymmetricAlgebra.functor 𝒪.obj ⋙
    moduleSheafification 𝒪

/-- The underlying module sheaf of the symmetric algebra on a commutative ringed site. -/
@[stacks 01CF "symmetric algebra on a ringed site"]
noncomputable abbrev sheaf
    (F : ringedSiteModuleCategory J 𝒪) : ringedSiteModuleCategory J 𝒪 :=
  (functor 𝒪).obj F

/-- The morphism on symmetric-algebra sheaves induced by a module-sheaf morphism. -/
noncomputable abbrev map
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    sheaf 𝒪 F ⟶ sheaf 𝒪 G :=
  (functor 𝒪).map f

/-- On underlying presheaves, the symmetric-algebra sheaf map is the sheafification of the
sectionwise symmetric-algebra map. -/
theorem map_eq_sheafification
    {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    map 𝒪 f = (moduleSheafification 𝒪).map (presheafMap 𝒪 f) := sorry

/-- The degree-one inclusion from a module sheaf to its symmetric-algebra sheaf. -/
noncomputable def ι (F : ringedSiteModuleCategory J 𝒪) : F ⟶ sheaf 𝒪 F :=
  (moduleSheafificationValIso 𝒪 F).inv ≫
    (moduleSheafification 𝒪).map (presheafι 𝒪 F)

/-- The degree-one inclusions into symmetric-algebra sheaves are natural in the module sheaf. -/
theorem ι_naturality {F G : ringedSiteModuleCategory J 𝒪} (f : F ⟶ G) :
    f ≫ ι 𝒪 G = ι 𝒪 F ≫ map 𝒪 f := sorry

/-- The degree-one inclusions satisfy the naturality equation in functorial form. -/
theorem unit_naturality (F G : ringedSiteModuleCategory J 𝒪) (f : F ⟶ G) :
    (𝟭 _).map f ≫ ι 𝒪 G = ι 𝒪 F ≫ (functor 𝒪).map f := sorry

/-- The canonical degree-one inclusion into the symmetric-algebra functor on module sheaves. -/
noncomputable def unit : 𝟭 _ ⟶ functor 𝒪 where
  app F := ι 𝒪 F
  naturality := fun {F G} f ↦ unit_naturality 𝒪 F G f

end SheafOfModules.RingedSite.SymmetricAlgebra
