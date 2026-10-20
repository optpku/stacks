/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassAction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell

/-!
# The Weierstrass quotient presentation of elliptic curves

The quotient of the discriminant-open Weierstrass scheme by admissible changes
of variables presents the moduli stack of elliptic curves. Its quotient atlas
agrees with the classifying morphism of the universal Weierstrass family.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CartesianMonoidalCategory MonoidalCategory FiberedCategoryOver.Groupoids
open scoped Bicategory CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

/-- The action groupoid of `H` acting on `W`. -/
def groupoid : GroupoidAlgebraicSpace terminalSpace :=
  GroupoidAlgebraicSpace.ofAction group action

/-- The object space of the action groupoid is the Weierstrass scheme. -/
theorem groupoid_U : groupoid.U = schemeAsOver :=
  rfl

/-- The arrow space of the action groupoid is `H × W`. -/
theorem groupoid_R : groupoid.R = (group.X ⊗ schemeAsOver) :=
  rfl

/-- The quotient stack `[W / H]` of the Weierstrass action. -/
def stack : GroupoidsOver EllipticCurve.Moduli.specInt :=
  GroupoidAlgebraicSpace.SmallQuotient.quotientStack groupoid

/-- `stack` is the quotient stack of the Weierstrass action groupoid. -/
theorem stack_eq : stack = GroupoidAlgebraicSpace.SmallQuotient.quotientStack groupoid :=
  rfl

/-- The atlas `W ⟶ [W / H]`. -/
def atlas : (AlgebraicSpace.ofOver WeierstrassScheme.overInt).toGroupoids ⟶ stack :=
  GroupoidAlgebraicSpace.SmallQuotient.atlas groupoid

/-- `atlas` is the atlas of the Weierstrass action groupoid. -/
theorem atlas_eq : atlas = GroupoidAlgebraicSpace.SmallQuotient.atlas groupoid :=
  rfl

end AlgebraicGeometry.AlgebraicStack.WeierstrassQuotient

namespace AlgebraicGeometry.EllipticCurve

/-- The quotient of the Weierstrass scheme by admissible changes of variables is equivalent
to the moduli stack of elliptic curves, compatibly with the universal family's classifying
morphism and the quotient atlas. -/
theorem equiv_weierstrassQuotient :
    ∃ e : AlgebraicStack.WeierstrassQuotient.stack ⟶ moduli.{u},
      (FiberedCategoryOver.Groupoids.toBasedFunctor e).IsEquivalence ∧
        Nonempty
          (AlgebraicStack.WeierstrassQuotient.atlas ≫ e ≅
            (AlgebraicSpace.ofOverSliceEquiv WeierstrassScheme.overInt).hom ≫
              WeierstrassScheme.classifying.{u}) :=
  sorry

end AlgebraicGeometry.EllipticCurve
