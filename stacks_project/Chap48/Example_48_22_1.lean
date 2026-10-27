/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingModule

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Example 48.22.1: let `A` be a local Noetherian ring, let
`f : X ⟶ Spec (CommRingCat.of A)` be proper. For a normalized `ωA`, the derived
quasicoherent pushforward has a genuine right adjoint `a`; the canonical affine tilde
of `ωA` is sent by `a` to a dualizing complex whose degree `-d` cohomology is a
dualizing module. -/
@[stacks 0AWI] #check
  (AlgebraicGeometry.Scheme.isDualizingModule_of_proper :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      {X : AlgebraicGeometry.Scheme.{u}}
      [hA₀ : HomotopyCategory.Koszul.TensorDescends (C := ModuleCat.{u} A)]
      [hA₁ : HomotopyCategory.KFlat.TensorDescends (C := ModuleCat.{u} A)]
      [hA₂ : DerivedCategory.KFlat.IsLocalization (C := ModuleCat.{u} A)]
      (HA : @MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) _
        (DerivedCategory.KFlat.monoidalCategory (C := ModuleCat.{u} A)))
      [hX₀ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
        X.toRingedSpace]
      [hX₁ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends
        X.toRingedSpace]
      [hX₂ : AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization
        X.toRingedSpace]
      (HX : @MonoidalClosed
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace) _
        (AlgebraicGeometry.RingedSpace.ModuleDerived.monoidalCategory
          X.toRingedSpace))
      (ωA : DerivedCategory (ModuleCat.{u} A))
      (hωA : ωA.IsNormalizedDualizingComplex HA)
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)) [IsProper f]
      (a : AlgebraicGeometry.Scheme.DerivedQCoh
        (AlgebraicGeometry.Spec (CommRingCat.of A)) ⥤ AlgebraicGeometry.Scheme.DerivedQCoh X)
      (aAdj : AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (d : ℕ) (h_dimension : topologicalKrullDim X = d),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule
        ((a.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde
          (CommRingCat.of A)).obj ωA)).obj) HX (-(d : ℤ))
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf
          ((a.obj ((AlgebraicGeometry.Scheme.DerivedQCoh.affineTilde
            (CommRingCat.of A)).obj ωA)).obj) (-(d : ℤ))))
