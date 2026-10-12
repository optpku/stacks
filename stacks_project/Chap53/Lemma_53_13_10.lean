/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Ramification
import StacksCheckRecall

universe u

open CategoryTheory

namespace AlgebraicGeometry.Curve

/- Lemma 53.13.10: for a closed point of a smooth curve after base change to an algebraic
closure, the ramification index of the canonical extension of stalks equals the finite
inseparable degree of the residue field of its image. -/
@[stacks 0C1G] #check
  (AlgebraicGeometry.Curve.baseChange_ramificationIdx_eq_finInsepDegree :
    ∀ {k kbar : Type u} [Field k] [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
      (X : SchemeOverField k) [Curve X] [Smooth X.hom]
      (xbar : FieldExtension.baseChange k kbar X.hom)
      (hxbar : xbar ∈ closedPoints (FieldExtension.baseChange k kbar X.hom)),
      let Xbar := FieldExtension.baseChange k kbar X.hom
      let x := FieldExtension.toSource k kbar X.hom xbar
      let X₀ := X.left
      (IsLocalRing.maximalIdeal (Xbar.presheaf.stalk xbar)).ramificationIdx
          (X₀.presheaf.stalk x) =
        Field.finInsepDegree k (X₀.residueField x))

end AlgebraicGeometry.Curve
