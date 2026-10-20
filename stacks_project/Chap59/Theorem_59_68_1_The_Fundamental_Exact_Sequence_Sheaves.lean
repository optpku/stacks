/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.FundamentalExactSequence

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale.Small
open CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom]

/- Compatibility checks for the declarations used by the higher-vanishing lemmas. -/
#check (genericPointInclusion X :
  Spec (X.left.residueField (genericPoint X.left)) ⟶ X.left)
#check (ClosedPoint X : Type u)

variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
    (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
    AddCommGrpCat.{u}]

#check (genericUnitsPushforward X :
  Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})

variable [∀ x : ClosedPoint X,
    HasSheafify (Spec (X.left.residueField x.1)).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproduct fun x : ClosedPoint X =>
    closedPointConstantZPushforward X x.1 x.2]

variable (x : X.left) (hx : x ∈ closedPoints X.left)
variable [HasSheafify (Spec (X.left.residueField x)).smallEtaleTopology AddCommGrpCat.{u}]

#check (closedPointConstantZPushforward X x hx :
  Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
#check (closedPointsCoproduct X :
  Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})

end AlgebraicGeometry.SchemeOverField
