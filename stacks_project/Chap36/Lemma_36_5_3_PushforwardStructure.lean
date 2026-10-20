/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- The underived direct image `f_*𝒪_X`, placed in degree zero, has quasicoherent
cohomology for a quasi-compact, quasi-separated morphism. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf_mem :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f],
      Scheme.ModuleDerived.quasicoherentProperty S
        ((DerivedCategory.singleFunctor S.toRingedSpace.Modules 0).obj
          ((RingedSpace.Hom.pushforward f.toShHom).obj
            (SheafOfModules.unit X.toRingedSpace.ringCatSheaf))))

/- The underived direct image `f_*𝒪_X`, placed in degree zero as a derived module
with quasicoherent cohomology. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f],
      Scheme.ModuleDerived.Quasicoherent S)

/- The underlying derived module of the bundled direct image is `f_*𝒪_X` placed in
degree zero. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf_obj :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f],
      (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf f).obj =
        (DerivedCategory.singleFunctor S.toRingedSpace.Modules 0).obj
          ((RingedSpace.Hom.pushforward f.toShHom).obj
            (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

end AlgebraicGeometry.Scheme.DerivedQCoh
