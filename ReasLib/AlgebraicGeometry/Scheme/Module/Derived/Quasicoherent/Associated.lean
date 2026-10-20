/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

/-!
# Associated modules in the derived quasicoherent category

This file places an associated module sheaf in degree zero as an object of the derived category
with quasicoherent cohomology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.Module.Associated

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme.DerivedQCoh.Associated

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The associated `𝒪_X`-module of `N`, placed in degree zero, has quasicoherent cohomology. -/
theorem single_mem (f : X ⟶ Spec (CommRingCat.of R)) (N : ModuleCat.{u} R) :
    Scheme.ModuleDerived.quasicoherentProperty X
      ((DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
        (obj (Scheme.Hom.globalSectionsMap f) N)) := sorry

/-- The associated `𝒪_X`-module of `N`, regarded as a degree-zero derived object with
quasicoherent cohomology. -/
noncomputable def single (f : X ⟶ Spec (CommRingCat.of R))
    (N : ModuleCat.{u} R) : Scheme.ModuleDerived.Quasicoherent X :=
  ⟨(DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
      (obj (Scheme.Hom.globalSectionsMap f) N),
    single_mem f N⟩

/-- The underlying derived object of `single f N` is the associated `𝒪_X`-module placed in
degree zero. -/
theorem single_obj (f : X ⟶ Spec (CommRingCat.of R)) (N : ModuleCat.{u} R) :
    (single f N).obj =
      (DerivedCategory.singleFunctor X.toRingedSpace.Modules (0 : ℤ)).obj
        (obj (Scheme.Hom.globalSectionsMap f) N) := sorry

end Scheme.DerivedQCoh.Associated
end AlgebraicGeometry
