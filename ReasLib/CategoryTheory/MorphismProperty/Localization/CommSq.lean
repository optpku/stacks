/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lifting commutative squares through fraction localizations

A commutative square in a localization can be represented by two compatible fractions and a
comparison morphism in the original category.  Named structures expose each part of the lifted
diagram directly and avoid positional unpacking of nested existential conjunctions.
-/

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory.MorphismProperty

namespace LeftFraction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasLeftCalculusOfFractions]
variable {X X' Y Y' : C}

/-- A representation in `C` of a commutative square in a left-fraction localization. -/
@[stacks 05Q3 "left-fraction lift of a localized commutative square"]
structure CommSqLift
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y') where
  /-- A left-fraction representative of the top morphism. -/
  aFraction : W.LeftFraction X X'
  /-- A left-fraction representative of the bottom morphism. -/
  bFraction : W.LeftFraction Y Y'
  /-- The comparison morphism between the targets of the two fractions. -/
  comparison : aFraction.Y' ⟶ bFraction.Y'
  /-- The numerator square in the original category. -/
  numeratorSquare : CommSq aFraction.f f comparison bFraction.f
  /-- The denominator square in the original category. -/
  denominatorSquare : CommSq aFraction.s f' comparison bFraction.s
  /-- The first fraction represents the top localized morphism. -/
  aMap : a = aFraction.map L (Localization.inverts L W)
  /-- The second fraction represents the bottom localized morphism. -/
  bMap : b = bFraction.map L (Localization.inverts L W)

namespace CommSqLift

/-- The pair of left-fraction representatives carried by a lifted square. -/
def fractionPair
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : L.obj X ⟶ L.obj X'} {b : L.obj Y ⟶ L.obj Y'}
    (e : CommSqLift L W f f' a b) :
    W.LeftFraction X X' × W.LeftFraction Y Y' :=
  (e.aFraction, e.bFraction)

end CommSqLift

/-- Every commutative square in a localization with a left calculus of fractions admits a
left-fraction lift in the original category. -/
@[stacks 05Q3]
theorem existsCommSqLift
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq a (L.map f) (L.map f') b) :
    Nonempty (CommSqLift L W f f' a b) := sorry

end LeftFraction

namespace RightFraction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable (L : C ⥤ D) (W : MorphismProperty C)
  [L.IsLocalization W] [W.HasRightCalculusOfFractions]
variable {X X' Y Y' : C}

/-- A representation in `C` of a commutative square in a right-fraction localization. -/
@[stacks 05Q7 "right-fraction lift of a localized commutative square"]
structure CommSqLift
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y') where
  /-- A right-fraction representative of the top morphism. -/
  aFraction : W.RightFraction X X'
  /-- A right-fraction representative of the bottom morphism. -/
  bFraction : W.RightFraction Y Y'
  /-- The comparison morphism between the sources of the two fractions. -/
  comparison : aFraction.X' ⟶ bFraction.X'
  /-- The denominator square in the original category. -/
  denominatorSquare : CommSq comparison aFraction.s bFraction.s f
  /-- The numerator square in the original category. -/
  numeratorSquare : CommSq aFraction.f comparison f' bFraction.f
  /-- The first fraction represents the top localized morphism. -/
  aMap : a = aFraction.map L (Localization.inverts L W)
  /-- The second fraction represents the bottom localized morphism. -/
  bMap : b = bFraction.map L (Localization.inverts L W)

namespace CommSqLift

/-- The pair of right-fraction representatives carried by a lifted square. -/
def fractionPair
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : L.obj X ⟶ L.obj X'} {b : L.obj Y ⟶ L.obj Y'}
    (e : CommSqLift L W f f' a b) :
    W.RightFraction X X' × W.RightFraction Y Y' :=
  (e.aFraction, e.bFraction)

end CommSqLift

/-- Every commutative square in a localization with a right calculus of fractions admits a
right-fraction lift in the original category. -/
@[stacks 05Q7]
theorem existsCommSqLift
    (f : X ⟶ Y) (f' : X' ⟶ Y')
    (a : L.obj X ⟶ L.obj X') (b : L.obj Y ⟶ L.obj Y')
    (hcomm : CommSq a (L.map f) (L.map f') b) :
    Nonempty (CommSqLift L W f f' a b) := sorry

end RightFraction

end CategoryTheory.MorphismProperty
