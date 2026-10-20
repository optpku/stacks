/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.RelativeEquivalence
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Determinant

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/-- The structure morphism of a Fourier–Mukai object is smooth. -/
instance FourierMukaiObject.instSmooth {S : Scheme.{u}} (X : FourierMukaiObject S) :
    Smooth X.hom :=
  X.smooth

/-- The structure morphism of a Fourier–Mukai object is proper. -/
instance FourierMukaiObject.instIsProper {S : Scheme.{u}} (X : FourierMukaiObject S) :
    IsProper X.hom :=
  X.proper

/-- An invertible perfect kernel between smooth proper schemes over a base induces
an equivalence on derived objects with quasi-coherent cohomology. -/
instance FourierMukaiObject.quasicoherentFunctor_isEquivalence
    {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)] :
    (Scheme.FourierMukai.quasicoherent X.hom Y.hom
      ((Scheme.PerfectDerived.toDerivedQCoh
        (Limits.pullback X.hom Y.hom)).obj K)).IsEquivalence := sorry

/-- An invertible perfect kernel between smooth proper schemes over a base induces
an equivalence on perfect derived objects. -/
instance FourierMukaiObject.perfectFunctor_isEquivalence
    {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)] :
    (Scheme.FourierMukai.perfect X.hom Y.hom K).IsEquivalence := sorry
