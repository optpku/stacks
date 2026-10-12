/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.RingTheory.LocalRing.Branches.Unibranch
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (x : X)
variable (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
  [IsHenselizationOf (X.presheaf.stalk x) Ah]
variable (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
  [IsStrictHenselizationOf (X.presheaf.stalk x) Ash]

/- Lemma 28.15.6 (1): the branch number of a scheme `X` at a point `x`, computed from a chosen
henselization of `X.presheaf.stalk x`, is `1` if and only if `X` is unibranch at `x`. -/
@[stacks 0C39] #check
  (BranchNumber.eq_one_iff_isUnibranch (A := X.presheaf.stalk x) (Ah := Ah) :
    X.branchNumberAt x Ah = 1 ↔ X.isUnibranchAt x)

/- Lemma 28.15.6 (2): the geometric branch number of a scheme `X` at a point `x`, computed from
a chosen strict henselization of `X.presheaf.stalk x`, is `1` if and only if `X` is geometrically
unibranch at `x`. -/
@[stacks 0C39] #check
  (GeometricBranchNumber.eq_one_iff_isGeometricallyUnibranch
      (A := X.presheaf.stalk x) (Ash := Ash) :
    X.geometricBranchNumberAt x Ash = 1 ↔ X.isGeometricallyUnibranchAt x)

end AlgebraicGeometry.Scheme
