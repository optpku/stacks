/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.StableVectorFields

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Lemma 53.26.3: every `k`-derivation of the structure sheaf of a proper, connected,
one-dimensional at-worst-nodal scheme of genus at least two with no rational tails or rational
bridges is zero. -/
@[stacks 0E69] #check (AlgebraicGeometry.Curve.derivation_eq_zero_of_stable :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (h_genus : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge X))
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)),
    derivationIsZero X D)

end AlgebraicGeometry.Curve
