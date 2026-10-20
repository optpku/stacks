/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Ideals from maps into the structure module

Any morphism from a module sheaf to the structure module induces a linear map from its stalk to
the stalk ring.  Its range is an ideal.  This generic owner is then specialized to subobjects of
the structure module without choosing new stalk representatives.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace ModuleStalkImage

/-- The map from the stalk of a module sheaf to the structure-sheaf stalk induced by a morphism
to the structure module. -/
noncomputable abbrev toRing {F : X.Modules}
    (f : F ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    RingedSpace.stalkModuleCat F x ⟶
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  RingedSpace.moduleStalkHom x f ≫ RingedSpace.unitStalkLinearMap x

/-- The image ideal in `𝒪_{X,x}` of a module-sheaf morphism into the structure module. -/
noncomputable def ideal {F : X.Modules}
    (f : F ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  LinearMap.range (toRing f x).hom

/-- Membership in `ideal f x` is witnessed by an element of the source stalk. -/
theorem mem_ideal_iff {F : X.Modules}
    (f : F ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X)
    (r : X.presheaf.stalk x) :
    r ∈ ideal f x ↔
      ∃ s : RingedSpace.stalkModuleCat F x, (toRing f x).hom s = r := sorry

/-- The map `toRing f x` sends the germ of a local section to the ring germ of its image under
`f`. -/
theorem toRing_germ {F : X.Modules}
    (f : F ⟶ SheafOfModules.unit X.ringCatSheaf) (x : X)
    (U : TopologicalSpace.Opens X) (hx : x ∈ U) (s : F.val.obj (Opposite.op U)) :
    toRing f x (TopCat.Presheaf.germ F.val.presheaf U x hx s) =
      X.presheaf.germ U x hx
        (SheafOfModules.unitSectionToRingSection U (f.val.app (Opposite.op U) s)) := sorry

end ModuleStalkImage

/-- The stalk map of a subobject of the unit module sheaf, viewed in the stalk ring through the
canonical unit-stalk identification. -/
noncomputable abbrev idealSheafStalkToRing
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) (x : X) :
    RingedSpace.stalkModuleCat (I : X.Modules) x ⟶
      ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x) :=
  ModuleStalkImage.toRing I.arrow x

/-- The image ideal in `𝒪_{X,x}` of the stalk map induced by a subobject of the unit module
sheaf. -/
noncomputable def idealSheafStalkIdeal
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf)) (x : X) :
    Ideal (X.presheaf.stalk x) :=
  ModuleStalkImage.ideal I.arrow x

/-- An element of `𝒪_{X,x}` lies in `idealSheafStalkIdeal I x` exactly when it is the image of
an element of the stalk of `I`. -/
theorem mem_idealSheafStalkIdeal_iff
    (I : Subobject (SheafOfModules.unit X.ringCatSheaf))
    (x : X) (r : X.presheaf.stalk x) :
    r ∈ idealSheafStalkIdeal I x ↔
      ∃ s : RingedSpace.stalkModuleCat (I : X.Modules) x,
        (idealSheafStalkToRing I x).hom s = r := sorry

end AlgebraicGeometry.RingedSpace
