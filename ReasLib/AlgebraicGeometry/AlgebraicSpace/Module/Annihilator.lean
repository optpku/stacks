/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Annihilator
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift

/-!
# Annihilator ideals of modules on algebraic spaces

The annihilator ideal is obtained from the kernel of the scalar action on the
universe-lifted module, transporting its section ideals back to the original
structure sheaf.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The section ideal of the annihilator over an étale object, recast from the
universe-lifted commutative presentation. -/
def annihilatorSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    Ideal ((structureSheaf X).obj.obj U) :=
  Ideal.comap (ULift.ringEquiv.{u, u + 1}.symm.toRingHom)
    (IdealSheaf.sections.{u + 1, u, u + 1}
      (SheafOfModules.RingedSite.Annihilator.subobject.{u + 1, u} (liftModule F)) U)

/-- The section ideal is the comap of the lifted annihilator section ideal along
the universe-lift ring equivalence. -/
theorem annihilatorSectionIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    annihilatorSectionIdeal F U =
      Ideal.comap (ULift.ringEquiv.{u, u + 1}.symm.toRingHom)
        (IdealSheaf.sections.{u + 1, u, u + 1}
          (SheafOfModules.RingedSite.Annihilator.subobject.{u + 1, u} (liftModule F)) U) :=
  rfl

/-- Restriction of annihilator sections remains in the annihilator. -/
theorem map_mem_annihilatorSectionIdeal {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) {U V : (smallEtaleSite X)ᵒᵖ} (f : U ⟶ V)
    (a : annihilatorSectionIdeal F U) :
    (structureSheaf X).obj.map f (a : (structureSheaf X).obj.obj U) ∈
      annihilatorSectionIdeal F V :=
  sorry

/-- The annihilator of `F` as an `𝒪_X`-module, with sections the annihilator
ideals of the universe-lifted presentation. -/
def annihilatorSheaf {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    X.Modules where
  val :=
    { obj := fun U => ModuleCat.of _ (annihilatorSectionIdeal F U)
      map := fun {U V} f =>
        ModuleCat.ofHom
          (Y :=
            (ModuleCat.restrictScalars ((structureSheaf X).obj.map f).hom).obj
              (ModuleCat.of _ (annihilatorSectionIdeal F V)))
          { toFun := fun a =>
              ⟨(structureSheaf X).obj.map f (a : (structureSheaf X).obj.obj U),
                map_mem_annihilatorSectionIdeal F f a⟩
            map_add' := sorry
            map_smul' := sorry }
      map_id := sorry
      map_comp := sorry }
  isSheaf := sorry

/-- The canonical inclusion of the annihilator sheaf into `𝒪_X`. -/
def annihilatorι {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    annihilatorSheaf F ⟶ SheafOfModules.unit (structureSheaf X) where
  val :=
    { app := fun U =>
        ModuleCat.ofHom
          (Submodule.subtype (annihilatorSectionIdeal F U : Submodule _ _))
      naturality := sorry }

/-- The annihilator inclusion is a monomorphism. -/
instance annihilatorι_mono {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) : Mono (annihilatorι F) :=
  sorry

/-- The component of the annihilator inclusion is the subtype inclusion of its
section ideal. -/
theorem annihilatorι_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) (U : (smallEtaleSite X)ᵒᵖ) :
    ((annihilatorι F).val.app U).hom =
      Submodule.subtype (annihilatorSectionIdeal F U : Submodule _ _) :=
  rfl

/-- The annihilator ideal of an `𝒪_X`-module, as the kernel of the scalar-action
map recast to `X.Modules`. -/
def annihilatorIdeal {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    IdealSubobject X :=
  Subobject.mk (annihilatorι F)

/-- The annihilator ideal is the subobject represented by the annihilator
inclusion. -/
theorem annihilatorIdeal_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (F : X.Modules) :
    annihilatorIdeal F = Subobject.mk (annihilatorι F) :=
  rfl

/-- The annihilator of a finite-type quasi-coherent `𝒪_X`-module is
quasi-coherent. -/
instance instIsQuasiCoherent_annihilatorIdeal {S : Scheme.{u}}
    {X : AlgebraicSpace S} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    IsQuasiCoherent (annihilatorIdeal F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
