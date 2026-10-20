/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Annihilator sheaf of a module on a ringed space

The annihilator `Ann(ℱ)` of an `𝒪_X`-module `ℱ` is the kernel of the canonical map
`𝒪_X → Hom(ℱ, ℱ)`. It is a subsheaf of the structure sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry Opposite TopologicalSpace

noncomputable section

universe u

namespace SheafOfModules

variable {X : RingedSpace.{u}}

namespace Annihilator

/-- The canonical map `𝒪_X → Hom(ℱ, ℱ)` whose kernel is the annihilator. -/
@[stacks 0H2H "canonical action map"]
noncomputable abbrev action (ℱ : X.Modules) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (ihom ℱ).obj ℱ :=
  SheafOfModules.RingedSite.Annihilator.action
    (J := Opens.grothendieckTopology X) (O := X.sheaf) ℱ

/-- The annihilator of `ℱ` as a subobject of the structure module.  This is the canonical owner;
its underlying module sheaf and inclusion are obtained from the subobject API. -/
@[stacks 0H2H "annihilator subobject"]
noncomputable abbrev subobject (ℱ : X.Modules) :
    Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  SheafOfModules.RingedSite.Annihilator.subobject
    (J := Opens.grothendieckTopology X) (O := X.sheaf) ℱ

end Annihilator

/-- The module sheaf underlying the annihilator subobject of `ℱ`. -/
@[stacks 0H2H "underlying module sheaf"]
abbrev annihilator (ℱ : X.Modules) : X.Modules :=
  Annihilator.subobject ℱ

namespace Annihilator

scoped notation:max "Ann(" ℱ ")" => SheafOfModules.annihilator ℱ

end Annihilator

open scoped Annihilator

namespace Annihilator

/-- The canonical inclusion of the annihilator into the structure sheaf. -/
@[stacks 0H2H "kernel inclusion"]
noncomputable abbrev ι (ℱ : X.Modules) :
    Ann(ℱ) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  SheafOfModules.RingedSite.Annihilator.ι
    (J := Opens.grothendieckTopology X) (O := X.sheaf) ℱ

/-- The annihilator inclusion followed by the scalar-action map is zero. -/
@[reassoc, stacks 0H2H "kernel equation"]
theorem ι_comp_action (ℱ : X.Modules) :
    ι ℱ ≫ action ℱ = 0 := sorry

/-- A morphism into the structure module factors through `Ann(ℱ)` exactly when it acts trivially
on `ℱ`. -/
@[stacks 0H2H "annihilator universal property"]
theorem factors_iff (ℱ : X.Modules) {K : X.Modules}
    (f : K ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (subobject ℱ).Factors f ↔ f ≫ action ℱ = 0 := sorry

/-- The canonical lift of a morphism annihilated by `action ℱ` to the annihilator module. -/
@[stacks 0H2H "annihilator lift"]
noncomputable abbrev lift (ℱ : X.Modules) {K : X.Modules}
    (f : K ⟶ SheafOfModules.unit X.ringCatSheaf) (h : f ≫ action ℱ = 0) :
    K ⟶ Ann(ℱ) :=
  SheafOfModules.RingedSite.Annihilator.lift
    (J := Opens.grothendieckTopology X) (O := X.sheaf) ℱ f h

/-- The annihilator lift followed by the kernel inclusion recovers the original morphism. -/
@[reassoc, stacks 0H2H "annihilator lift equation"]
theorem lift_ι (ℱ : X.Modules) {K : X.Modules}
    (f : K ⟶ SheafOfModules.unit X.ringCatSheaf) (h : f ≫ action ℱ = 0) :
    lift ℱ f h ≫ ι ℱ = f := sorry

/-- Morphisms into `Ann(ℱ)` are determined by their composites with the kernel inclusion. -/
@[ext, stacks 0H2H "annihilator morphism extensionality"]
theorem hom_ext (ℱ : X.Modules) {K : X.Modules} {f g : K ⟶ Ann(ℱ)}
    (h : f ≫ ι ℱ = g ≫ ι ℱ) : f = g := sorry

/-- Isomorphic module sheaves have isomorphic annihilator modules. -/
@[stacks 0H2H "annihilator isomorphism"]
noncomputable abbrev mapIso {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) : Ann(ℱ) ≅ Ann(𝒢) :=
  SheafOfModules.RingedSite.Annihilator.mapIso
    (J := Opens.grothendieckTopology X) (O := X.sheaf) e

/-- The annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "annihilator isomorphism inclusion"]
theorem mapIso_hom_ι {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) :
    (mapIso e).hom ≫ ι 𝒢 = ι ℱ := sorry

/-- The inverse annihilator isomorphism commutes with the canonical inclusions. -/
@[reassoc, stacks 0H2H "inverse annihilator isomorphism inclusion"]
theorem mapIso_inv_ι {ℱ 𝒢 : X.Modules} (e : ℱ ≅ 𝒢) :
    (mapIso e).inv ≫ ι ℱ = ι 𝒢 := sorry

/-- The identity module isomorphism induces the identity annihilator isomorphism. -/
@[simp, stacks 0H2H "annihilator identity isomorphism"]
theorem mapIso_refl (ℱ : X.Modules) :
    mapIso (Iso.refl ℱ) = Iso.refl (Ann(ℱ)) := sorry

/-- Annihilator isomorphisms respect composition of module-sheaf isomorphisms. -/
@[simp, stacks 0H2H "annihilator composition isomorphism"]
theorem mapIso_trans {ℱ 𝒢 ℋ : X.Modules} (e : ℱ ≅ 𝒢) (e' : 𝒢 ≅ ℋ) :
    mapIso (e.trans e') = (mapIso e).trans (mapIso e') := sorry

/-- A section of the annihilator, viewed as a section of `𝒪_X` via the kernel inclusion. -/
abbrev sectionToRing (ℱ : X.Modules) (U : Opens X)
    (s : (Ann(ℱ)).val.obj (op U)) : X.presheaf.obj (op U) :=
  unitSectionToRingSection U ((ι ℱ).val.app (op U) s)

/-- A local section of the annihilator acts as zero on every local section of the module sheaf. -/
@[stacks 0H2I "sectionwise annihilation"]
theorem sectionToRing_smul_eq_zero
    (ℱ : X.Modules) (U : Opens X)
    (s : (Ann(ℱ)).val.obj (op U)) (m : ℱ.val.obj (op U)) :
    sectionToRing ℱ U s • m = 0 := sorry

end Annihilator

end SheafOfModules

-- The morphism, kernel, and isomorphism payloads above are explicit.  Any inherited `sorryAx` is
-- confined to Prop-valued kernel/isomorphism laws and the canonical monoidal comparison owners.
