/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- The ambient Fourier--Mukai transform is provided by the shared mathematical owner. -/
#check
  (AlgebraicGeometry.Scheme.FourierMukai.functor :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace),
      RingedSpace.ModuleDerived X.toRingedSpace ⥤
        RingedSpace.ModuleDerived Y.toRingedSpace)

end AlgebraicGeometry.Scheme.FourierMukai
