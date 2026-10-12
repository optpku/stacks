/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections.Pushforward.Cohomology

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The canonical map `H^i(Y, 𝒪_Y) ⟶ H^i(X, 𝒪_X)` induced by a scheme morphism
`g : X ⟶ Y`, with scalars on the target restricted along the map on global sections. -/
noncomputable def structureSheafCohomologyMap {X Y : Scheme.{u}}
    (g : X ⟶ Y) (i : ℕ) :=
  RingedSpace.Module.Derived.GlobalSections.Bounded.cohomologyMapOfFMap g.toShHom
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) i

end AlgebraicGeometry.Scheme.Hom
