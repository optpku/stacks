/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Variety.FundamentalExactSequence
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Units
public import ReasLib.CategoryTheory.Sites.HigherDirectImage

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Etale.Small
  CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

/-- For a smooth curve over an algebraically closed field, small-etale cohomology with
coefficients in the multiplicative group sheaf vanishes in every degree at least two. -/
@[stacks 03RM]
theorem etaleUnitsCohomology_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (q : Nat) (hq : 2 <= q) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj
      (unitsAddSheaf X.left)) := sorry

/-- For a smooth curve over an algebraically closed field, every positive higher direct
image of the multiplicative group sheaf along the generic-point inclusion is zero. -/
theorem genericUnits_higherDirectImage_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify
      (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasInjectiveResolutions
      (Sheaf (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
        AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q) :
    IsZero
      (Sheaf.higherDirectImage
        (Scheme.smallEtalePullback (X.left.fromSpecResidueField (genericPoint X.left)))
        (unitsAddSheaf (Spec (X.left.residueField (genericPoint X.left)))) q :
        Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}) := sorry

/-- For a smooth curve over an algebraically closed field, small-étale cohomology of
the direct image of generic-point units vanishes in every positive degree. -/
theorem genericUnitsPushforward_etaleCohomology_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify
      (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (p : ℕ) (hp : 0 < p) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology p).obj
      (genericUnitsPushforward X)) := sorry

/-- For a smooth curve over an algebraically closed field, small-étale cohomology of
the coproduct of the direct images of constant integer sheaves at all closed points
vanishes in every positive degree. -/
@[stacks 03RL]
theorem closedPointsCoproduct_etaleCohomology_isZero
    {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
    [Curve X] [Smooth X.hom]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ x : ClosedPoint X, HasSheafify (Spec (X.left.residueField x.1)).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasCoproduct fun x : ClosedPoint X ↦ closedPointConstantZPushforward X x.1 x.2]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (q : ℕ) (hq : 0 < q) :
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj
      (closedPointsCoproduct X)) := sorry

end AlgebraicGeometry.SchemeOverField
