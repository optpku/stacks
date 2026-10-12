/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.GlobalSections

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

#check (derivedQuasiCoherentModuleProperty X :
  ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))

#check (DerivedQCoh X : Type (u + 1))

#check (DerivedQCoh.inclusion X :
  DerivedQCoh X ⥤ RingedSpace.ModuleDerived X.toRingedSpace)

end AlgebraicGeometry.Scheme
