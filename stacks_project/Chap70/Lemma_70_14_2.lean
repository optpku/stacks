/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ideal.Torsion
import StacksCheckRecall

/-!
# Sections annihilated by a finite type ideal on an algebraic space

The ideal-torsion subsheaf is quasi-coherent, and its affine sections and geometric-point
stalks are the corresponding annihilators.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Lemma 70.14.2 (1): the ideal-torsion subsheaf is quasi-coherent. -/
@[stacks 0856] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheaf_isQuasicoherent :
    ∀ (I : IdealSubobject X) (ℱ : X.Modules),
      [(I : X.Modules).IsQuasicoherent] → [(I : X.Modules).IsFiniteType] →
      [ℱ.IsQuasicoherent] → (idealTorsionSubsheaf I ℱ).IsQuasicoherent)

/- Lemma 70.14.2 (2): affine sections are annihilated by the ideal sections. -/
@[stacks 0856] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.range_idealTorsionSubsheafι_app_eq_affine_annihilatedSections :
    ∀ (I : IdealSubobject X) (ℱ : X.Modules),
      [(I : X.Modules).IsQuasicoherent] → [(I : X.Modules).IsFiniteType] →
      [ℱ.IsQuasicoherent] → ∀ (U : affineEtaleSite X),
      Set.range ((idealTorsionSubsheafι I ℱ).val.app (op U.obj)) =
        setOf (fun s ↦ ∀ a, a ∈ SheafOfModules.Subobject.sections I (op U.obj) → a • s = 0))

/- Lemma 70.14.2 (3): stalk sections are annihilated by the ideal germs. -/
@[stacks 0856] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.range_idealTorsionSubsheafι_stalk_eq_annihilatedStalkSections :
    ∀ (I : IdealSubobject X) (ℱ : X.Modules),
      [(I : X.Modules).IsQuasicoherent] → [(I : X.Modules).IsFiniteType] →
      [ℱ.IsQuasicoherent] → ∀ (xbar : GeometricPoint X),
      Set.range (stalkMap xbar (idealTorsionSubsheafι I ℱ)) =
        setOf (isAnnihilatedByIdealStalk I ℱ xbar))
