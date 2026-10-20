module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.AlgebraicGeometry.Scheme.Variety.FundamentalExactSequence
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme.Etale.Small
open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (X : SchemeOverField k) [Curve X] [Smooth X.hom]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify
    (Spec (X.left.residueField (genericPoint X.left))).smallEtaleTopology
    AddCommGrpCat.{u}]
variable [∀ x : ClosedPoint X,
    HasSheafify (Spec (X.left.residueField x.1)).smallEtaleTopology AddCommGrpCat.{u}]
variable [IsLocallyNoetherian X.left]
variable [HasCoproduct fun x : ClosedPoint X ↦
    closedPointConstantZPushforward X x.1 x.2]

/- Theorem 59.68.1 (The Fundamental Exact Sequence) -/
@[stacks 03RI] #check
  (AlgebraicGeometry.SchemeOverField.fundamentalExactSequence X :
    (AlgebraicGeometry.SchemeOverField.fundamentalShortComplex X).ShortExact)

end AlgebraicGeometry.SchemeOverField
