module

public import stacks_project.Chap91.«91_4_5_1_SquareZero»
public import ReasLib.AlgebraicGeometry.RingedSpace.FirstOrderThickening.Splitting
import StacksCheckRecall

/-!
# Splitting a trivialized first-order thickening of ringed spaces

A left inverse of a first-order thickening splits its structure sheaf as a
square-zero extension by the ideal module.
-/

universe u

open CategoryTheory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/- 91.4.5.1 -/
@[stacks 08LA] #check (AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.splittingIso :
  {X X' : RingedSpace.{u}} → {i : X ⟶ X'} → [IsFirstOrderThickening i] →
    (π : X' ⟶ X) → i ≫ π = 𝟙 X →
      CategoryTheory.Iso (pushforwardSheaf π) (squareZeroSheaf (idealModule i)))

#check AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.splittingIso_fst
#check AlgebraicGeometry.RingedSpace.IsFirstOrderThickening.splittingIso_inl

end AlgebraicGeometry.RingedSpace
