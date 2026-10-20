/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/-- The Fourier--Mukai transform preserves quasicoherent cohomology when the first structural
morphism is quasi-compact and quasi-separated and the kernel has quasicoherent cohomology. -/
theorem mapsTo {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
    (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K) :
    Scheme.ModuleDerived.quasicoherentProperty X ≤
      (Scheme.ModuleDerived.quasicoherentProperty Y).inverseImage
        (functor f g K) := sorry

/-- The Fourier--Mukai transform restricted to complexes with quasicoherent cohomology. -/
noncomputable def quasicoherent {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (K : Scheme.DerivedQCoh (Limits.pullback f g)) :
    Scheme.DerivedQCoh X ⥤ Scheme.DerivedQCoh Y :=
  (Scheme.ModuleDerived.quasicoherentProperty Y).lift
    ((Scheme.ModuleDerived.quasicoherentProperty X).ι ⋙
      functor f g K.obj)
    (fun E ↦ (mapsTo f g K.obj K.property) E.obj E.property)

/-- Forgetting the quasicoherent Fourier--Mukai restriction recovers the ambient transform. -/
noncomputable def quasicoherent_inclusionIso {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (K : Scheme.DerivedQCoh (Limits.pullback f g)) :
    quasicoherent f g K ⋙ Scheme.DerivedQCoh.inclusion Y ≅
      Scheme.DerivedQCoh.inclusion X ⋙ functor f g K.obj :=
  (Scheme.ModuleDerived.quasicoherentProperty Y).liftCompιIso
    ((Scheme.ModuleDerived.quasicoherentProperty X).ι ⋙ functor f g K.obj)
    (fun E ↦ (mapsTo f g K.obj K.property) E.obj E.property)

end AlgebraicGeometry.Scheme.FourierMukai
