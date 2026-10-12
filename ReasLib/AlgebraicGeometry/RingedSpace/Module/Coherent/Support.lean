/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support

/-!
# Coherent module sheaves with prescribed support

This file defines the object property and full subcategory of coherent module sheaves whose
set-theoretic support is contained in a prescribed subset.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.Coh

/-- The object property of coherent module sheaves supported on `T`. -/
def supportedOn {X : RingedSpace.{u}} (T : Set X) : ObjectProperty (RingedSpace.Coh X) :=
  (RingedSpace.moduleSupportedOn T).inverseImage
    (SheafOfModules.isCoherent X.ringCatSheaf).ι

/-- Membership in `supportedOn T` is containment of the module support in `T`. -/
theorem supportedOn_iff {X : RingedSpace.{u}} (T : Set X) (F : RingedSpace.Coh X) :
    supportedOn T F ↔ RingedSpace.moduleSupport F.obj ⊆ T := sorry

end AlgebraicGeometry.RingedSpace.Coh

namespace AlgebraicGeometry.RingedSpace

/-- The full subcategory of coherent module sheaves supported on `T`. -/
abbrev CohSupportedOn (X : RingedSpace.{u}) (T : Set X) :=
  (Coh.supportedOn T).FullSubcategory

namespace CohSupportedOn

/-- The underlying module of an object of `CohSupportedOn X T` has support contained in `T`. -/
theorem support_subset {X : RingedSpace.{u}} {T : Set X}
    (F : CohSupportedOn X T) : RingedSpace.moduleSupport F.obj.obj ⊆ T := sorry

end CohSupportedOn

end AlgebraicGeometry.RingedSpace
