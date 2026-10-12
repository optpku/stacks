/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity
import StacksCheckRecall

/-!
# Compatibility facade for Definition 31.20.2

The reusable ideal-sheaf regularity declarations, including the four labelled
conditions of Definition 31.20.2, are owned by
`ReasLib.AlgebraicGeometry.RingedSpace.Module.Regularity`. The Chapter 18
and 20 imports preserve the historical ideal-sheaf API
available through this file.
-/

@[expose] public section

universe u

/- Definition 31.20.2 (1): regular ideal sheaves are represented by the reusable
ringed-space predicate. -/
@[stacks 063D] #check
  (AlgebraicGeometry.RingedSpace.IsRegularIdealSheaf :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}},
      CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf) → Prop)

/- Definition 31.20.2 (2): Koszul-regular ideal sheaves are represented by the reusable
ringed-space predicate. -/
@[stacks 063D] #check
  (AlgebraicGeometry.RingedSpace.IsKoszulRegularIdealSheaf :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}},
      CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf) → Prop)

/- Definition 31.20.2 (3): `H₁`-regular ideal sheaves are represented by the reusable
ringed-space predicate. -/
@[stacks 063D] #check
  (AlgebraicGeometry.RingedSpace.IsH1RegularIdealSheaf :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}},
      CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf) → Prop)

/- Definition 31.20.2 (4): quasi-regular ideal sheaves are represented by the reusable
ringed-space predicate. -/
@[stacks 063D] #check
  (AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}},
      CategoryTheory.Subobject (SheafOfModules.unit X.ringCatSheaf) → Prop)
