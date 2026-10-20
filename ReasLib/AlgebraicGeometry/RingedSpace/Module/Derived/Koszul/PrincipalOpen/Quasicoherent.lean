/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul

/-- For a derived module on an affine scheme with quasi-coherent cohomology, the
powered-Koszul colimit comparison with degree-zero cohomology on the associated
finite union of principal opens is an isomorphism. -/
instance homColimitToOpenH0_isIso {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A)
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty (Spec (CommRingCat.of A)).toRingedSpace)) :
    IsIso (homColimitToOpenH0 f E.obj) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul
