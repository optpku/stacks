/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.SchemeOverField.PerfectDerived

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- A functor `PerfectDerived X ⥤ PerfectDerived Y` is a Fourier--Mukai functor with
perfect kernel if it is isomorphic to the restricted Fourier--Mukai transform of some
perfect object on the fibre product `X ×_k Y`. -/
def IsPerfectFourierMukai {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsProper X.hom] [IsProper Y.hom]
    (F : PerfectDerived X ⥤ PerfectDerived Y) : Prop :=
  ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace),
    Nonempty (F ≅ Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K)

/-- A perfect Fourier--Mukai functor is isomorphic to the restricted transform of some
perfect kernel. -/
theorem IsPerfectFourierMukai.exists_kernel {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsProper X.hom] [IsProper Y.hom]
    {F : PerfectDerived X ⥤ PerfectDerived Y} (hF : IsPerfectFourierMukai F) :
    ∃ (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace),
      Nonempty (F ≅ Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) := hF

/-- The restricted Fourier--Mukai transform of a perfect kernel is a perfect
Fourier--Mukai functor. -/
theorem IsPerfectFourierMukai.ofKernel {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsProper X.hom] [IsProper Y.hom]
    (K : @RingedSpace.ModuleDerived.Perfect (Limits.pullback X.hom Y.hom).toRingedSpace) :
    IsPerfectFourierMukai (Scheme.FourierMukai.perfectNoetherian X.hom Y.hom K) := ⟨K, ⟨Iso.refl _⟩⟩

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
