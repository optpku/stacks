/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.AssociatedGraded
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Graded

/-!
# Cohomology of coherent formal modules

This file records uniform cohomology vanishing for twists of the transition kernels of a
coherent formal module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- For a coherent formal module along the pullback of an ideal from a Noetherian affine base,
the first cohomology of every transition kernel vanishes after one uniformly sufficient ample
twist. -/
theorem transitionKernel_twist_H1_eventually_isZero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A)
    [MonoidalCategory X.Modules] (L : X.Modules) [Modules.Invertible L] [Modules.IsAmple L]
    (F : CoherentFormalModules X ((idealSheafDataOfIdealOnSpec I).comap f)) :
    ∃ d0 : ℤ, ∀ n : ℕ, ∀ d : ℤ, d0 ≤ d →
      IsZero (RingedSpace.moduleCohomology
        (Modules.twistByTensorPower L (kernel (((F.obj).stepMap n).hom)) d) 1) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
