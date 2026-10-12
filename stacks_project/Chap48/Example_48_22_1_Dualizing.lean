/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualizingModule
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ExceptionalInverseImage
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open CategoryTheory

noncomputable section

universe u

#check AlgebraicGeometry.Scheme.ExceptionalInverseImage

#check AlgebraicGeometry.Scheme.ExceptionalInverseImage.ofAdjunction

#check AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule

#check AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule.ofLeftmostCohomology

#check AlgebraicGeometry.RingedSpace.ModuleDerived.isDualizingModule_iff
