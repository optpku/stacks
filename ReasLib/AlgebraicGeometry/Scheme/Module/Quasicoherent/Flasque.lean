/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Flasque injective quasicoherent modules

This module records flasqueness of injective quasicoherent modules on Noetherian schemes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- An injective quasicoherent module on a Noetherian scheme is flasque as a sheaf of modules. -/
theorem flasque_of_injective {X : Scheme.{u}} [IsNoetherian X]
    (ℐ : QCoh X) [Injective ℐ] :
    RingedSpace.Modules.flasque X.toRingedSpace ((inclusion X).obj ℐ) := sorry

/-- The underlying additive sheaf of an injective quasicoherent module on a Noetherian scheme
has its canonical flasque instance. -/
instance underlyingIsFlasque {X : Scheme.{u}} [IsNoetherian X]
    (ℐ : QCoh X) [Injective ℐ] :
    TopCat.Sheaf.IsFlasque
      ((RingedSpace.moduleUnderlyingSheaf X.toRingedSpace).obj ((inclusion X).obj ℐ)) :=
  flasque_of_injective ℐ

end AlgebraicGeometry.Scheme.QCoh
