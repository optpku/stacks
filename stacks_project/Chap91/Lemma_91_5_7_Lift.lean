/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatOver
public import stacks_project.Chap91.«91_3_1_1_Arrow»
public import stacks_project.Chap91.Remark_91_4_7_Thickening

/-!
# Flat lifts of an `𝒪_X`-module along a morphism of first-order thickenings

A flat lift of an `𝒪_X`-module `F` along `(f, f')` is an `𝒪_{X'}`-module `F'` which is
flat over `S'` and restricts to `F` along `i`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace (Modules)
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Thickening.Hom

/-- An `𝒪_{X'}`-module flat over `S'` whose inverse image along the first-order thickening
`i` is the given `𝒪_X`-module `F`. -/
structure FlatLift {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
    (g : T ⟶ U) (F : T.left.Modules) where
  /-- The lifted `𝒪_{X'}`-module `F'`. -/
  module : T.right.Modules
  /-- The lift is flat over `S'`. -/
  isFlatOver : SheafOfModules.IsFlatOver module g.right
  /-- Inverse image along `i` recovers `F`. -/
  restrictIso : (T.hom^*).obj module ≅ F

namespace FlatLift

variable {T U : Thickening.{u}} [IsFirstOrderThickening T.hom]
variable (g : T ⟶ U) (F : T.left.Modules)

/-- Assemble a flat lift from an `𝒪_{X'}`-module, relative flatness over `S'`, and an
isomorphism `i^* F' ≅ F`. -/
def of (module : T.right.Modules)
    (isFlatOver : SheafOfModules.IsFlatOver module g.right)
    (restrictIso : (T.hom^*).obj module ≅ F) : FlatLift g F where
  module := module
  isFlatOver := isFlatOver
  restrictIso := restrictIso

/-- A flat lift is an `𝒪_{X'}`-module flat over `S'` with `i^* F' ≅ F`. -/
theorem spec (L : FlatLift g F) :
    SheafOfModules.IsFlatOver L.module g.right ∧
      Nonempty ((T.hom^*).obj L.module ≅ F) := sorry

end FlatLift

end AlgebraicGeometry.RingedSpace.Thickening.Hom
