/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- The property that every cohomology sheaf of a derived module on a scheme is
quasicoherent. -/
abbrev quasicoherentProperty (X : Scheme.{u}) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  DerivedCategory.cohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

/-- The full subcategory of derived modules on a scheme whose cohomology sheaves are
quasicoherent. -/
abbrev Quasicoherent (X : Scheme.{u}) :=
  DerivedCategory.CohomologyIn
    (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)

namespace Quasicoherent

/-- The inclusion of derived modules with quasicoherent cohomology into all derived modules. -/
abbrev inclusion (X : Scheme.{u}) :
    Quasicoherent X ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  (quasicoherentProperty X).ι

end Quasicoherent

end AlgebraicGeometry.Scheme.ModuleDerived

namespace AlgebraicGeometry.Scheme

/-- The property that every cohomology sheaf of a derived module on a scheme is
quasicoherent. -/
abbrev derivedQuasiCoherentModuleProperty (X : Scheme.{u}) :
    ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace) :=
  ModuleDerived.quasicoherentProperty X

/-- The full subcategory of derived modules on a scheme whose cohomology sheaves are
quasicoherent. -/
abbrev DerivedQCoh (X : Scheme.{u}) :=
  ModuleDerived.Quasicoherent X

namespace DerivedQCoh

/-- The inclusion of derived modules with quasicoherent cohomology into all derived modules. -/
abbrev inclusion (X : Scheme.{u}) :
    DerivedQCoh X ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  ModuleDerived.Quasicoherent.inclusion X

end DerivedQCoh

end AlgebraicGeometry.Scheme
