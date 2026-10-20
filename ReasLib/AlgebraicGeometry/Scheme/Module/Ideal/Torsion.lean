/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Torsion
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine

/-!
# Torsion by finite type ideal sheaves on schemes

This file records the affine, quasicoherent, and stalkwise descriptions of the subsheaf
annihilated by an ideal sheaf of finite type.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The subsheaf of a module sheaf consisting of sections annihilated by an ideal sheaf. -/
noncomputable abbrev idealTorsionSubsheaf
    (I : X.IdealSheafData) (ℱ : X.Modules) : X.Modules :=
  Subobject.underlying.obj
    (SheafOfModules.RingedSite.IdealSheaf.torsionSubobject I.toSubobject ℱ)

/-- The canonical inclusion of the ideal-torsion subsheaf into its ambient module sheaf. -/
noncomputable abbrev idealTorsionSubsheafι
    (I : X.IdealSheafData) (ℱ : X.Modules) : idealTorsionSubsheaf I ℱ ⟶ ℱ :=
  (SheafOfModules.RingedSite.IdealSheaf.torsionSubobject I.toSubobject ℱ).arrow

/-- On an affine open, the image of the inclusion of the subsheaf annihilated by a finite type
ideal sheaf consists exactly of the sections annihilated by every section of the ideal. -/
theorem range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((Subobject.underlying.obj I.toSubobject : X.Modules).IsFiniteType)]
    (U : X.affineOpens) :
    Set.range
        (((idealTorsionSubsheafι I ℱ).val.app (Opposite.op U.1)).hom) =
      {s : Γ(ℱ, U.1) | ∀ a : Γ(X, U.1), a ∈ I.ideal U → a • s = 0} := sorry

/-- The subsheaf annihilated by a finite type ideal sheaf inside a quasicoherent module on a
scheme is quasicoherent. -/
theorem idealTorsionSubsheaf_isQuasicoherent
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((Subobject.underlying.obj I.toSubobject : X.Modules).IsFiniteType)] :
    (idealTorsionSubsheaf I ℱ).IsQuasicoherent := sorry

/-- At a point, the image of the stalk map from the subsheaf annihilated by a finite type ideal
sheaf consists exactly of the stalk sections annihilated by its stalk ideal. -/
theorem range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (I : X.IdealSheafData)
    [((Subobject.underlying.obj I.toSubobject : X.Modules).IsFiniteType)]
    (x : X) :
    Set.range ((RingedSpace.moduleStalkHom x
        (idealTorsionSubsheafι I ℱ)).hom) =
      {s : RingedSpace.stalkModuleCat ℱ x |
        ∀ a : X.presheaf.stalk x,
          a ∈ RingedSpace.idealSheafStalkIdeal I.toSubobject x → a • s = 0} := sorry

end AlgebraicGeometry.Scheme.Modules
