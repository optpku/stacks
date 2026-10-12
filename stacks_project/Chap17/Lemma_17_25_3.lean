/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 17.25.3: for a morphism of ringed spaces `f : X ⟶ Y`, the pullback of an invertible
`𝒪_Y`-module is invertible. -/
@[stacks 0B8L]
#check fun {X Y : RingedSpace.{u}} (f : X ⟶ Y) (L : Y.Modules)
    [MonoidalCategory.isInvertibleObject L] ↦
  (inferInstance :
    MonoidalCategory.isInvertibleObject ((RingedSpace.Hom.pullback f).obj L))
