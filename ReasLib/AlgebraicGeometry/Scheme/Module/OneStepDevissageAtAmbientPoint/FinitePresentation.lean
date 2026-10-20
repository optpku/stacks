/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.AtPoint
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Finite.Stalk

/-!
# Finite presentation in a one-step dévissage at an ambient point

This file records finite-presentation comparisons associated to a one-step
dévissage whose distinguished source point need not lie in the fibre support.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint

variable {S : Scheme.{u}} {X : Over S} {F : X.left.Modules}
  [LocallyOfFiniteType X.hom] [F.IsQuasicoherent] [F.IsFiniteType] {x : X.left}

/-- The finite map in an ambient-point one-step dévissage is of finite presentation
when the source scheme is locally of finite presentation over the base. -/
theorem piFinitePresentation (D : OneStepDevissageAtAmbientPoint X F x)
    [LocallyOfFinitePresentation X.hom] :
    Scheme.Hom.FinitePresentation D.toOneStepDevissage.π.left := sorry

/-- In an ambient-point one-step dévissage, finite presentation near the source point,
the distinguished auxiliary point, and its image under the finite map are equivalent. -/
theorem finitePresentationAt_tfae (D : OneStepDevissageAtAmbientPoint X F x)
    [LocallyOfFinitePresentation X.hom] :
    List.TFAE
      [ IsFinitePresentationAt F x
      , IsFinitePresentationAt D.toOneStepDevissage.G D.z
      , IsFinitePresentationAt
          ((Scheme.Modules.pushforward D.toOneStepDevissage.π.left).obj
            D.toOneStepDevissage.G) D.y
      ] := sorry

/-- In an ambient-point one-step dévissage, finite presentation of the three
distinguished stalk modules over their respective local rings is equivalent. -/
theorem stalkFinitePresentation_tfae (D : OneStepDevissageAtAmbientPoint X F x)
    [LocallyOfFinitePresentation X.hom] :
    List.TFAE
      [ Module.FinitePresentation (X.left.presheaf.stalk x)
          (RingedSpace.stalkModuleCat F x)
      , Module.FinitePresentation (D.toOneStepDevissage.Z.left.presheaf.stalk D.z)
          (RingedSpace.stalkModuleCat D.toOneStepDevissage.G D.z)
      , Module.FinitePresentation (D.toOneStepDevissage.Y.left.presheaf.stalk D.y)
          (RingedSpace.stalkModuleCat
            ((Scheme.Modules.pushforward D.toOneStepDevissage.π.left).obj
              D.toOneStepDevissage.G) D.y)
      ] := sorry

end AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint
