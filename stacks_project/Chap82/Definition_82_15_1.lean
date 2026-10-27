/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Quotient
import StacksCheckRecall

/-!
# Definition 82.15.1

Rational equivalence of `k`-cycles on a good algebraic space, and the Chow
group `CH_k(X) = Z_k(X) / ∼_rat`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Hom

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {B X : AlgebraicSpace S}
  [UniversallyCatenary B] [IsQuasiSeparated B]
variable (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
variable (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)

/- Definition 82.15.1 (1): In Situation 82.2.1, for good `X / B` and `k ∈ ℤ`, a
locally finite collection `{W_j ⊂ X}` of integral closed subspaces with
`dim_δ(W_j) = k + 1` and units `φ_j ∈ R(W_j)ˣ` determine the `k`-cycle
`∑ (i_j)_* div(φ_j) = RationalEquivalence.boundary f δ k W hWint hWdim φ hlocal`
in `Z_k(X)`, where `i_j` is the inclusion of `W_j`. This is well-defined because
the coproduct of the inclusions is proper. -/
@[stacks 0EQ6]
#check
  (AlgebraicGeometry.AlgebraicSpace.RationalEquivalence.boundary f δ k :
    {J : Type v} → (W : J → ClosedSubspace X) →
      (hWint : ∀ j, IsIntegral (W j).X) →
      (hWdim : ∀ j, AlgebraicGeometry.AlgebraicSpace.Hom.deltaDimension f δ
          (@ClosedSubspace.irreducibleClosed S X (W j) (hWint j)) = k + 1) →
      (φ : ∀ j, (RationalFunction (W j).X)ˣ) →
      (hlocal : LocallyFinite fun j ↦ (W j).pointsSet) →
        AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k)

/- Definition 82.15.1 (2): In Situation 82.2.1, a cycle `α ∈ Z_k(X)` is
rationally equivalent to zero when it is a cycle of the form displayed in
(1). -/
@[stacks 0EQ6]
#check
  (AlgebraicGeometry.AlgebraicSpace.RationalEquivalence.IsRationallyTrivial f δ k :
    AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k → Prop)

/- Definition 82.15.1 (3): In Situation 82.2.1, cycles `α, β ∈ Z_k(X)` are
rationally equivalent, written `α ∼_rat β`, when `α - β` is rationally
equivalent to zero. -/
@[stacks 0EQ6]
#check
  (AlgebraicGeometry.AlgebraicSpace.RationalEquivalence.RationallyEquivalent f δ k :
    AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k → AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup f δ k → Prop)

/- Definition 82.15.1 (4): In Situation 82.2.1, the Chow group of `k`-cycles on
`X` is `CH_k(X) = Z_k(X) / ∼_rat = Hom.chowGroup f δ k`. This is sometimes
called the Chow group of `k`-cycles modulo rational equivalence on `X`. -/
@[stacks 0EQ6]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowGroup f δ k : Type (u + 1))

end

end AlgebraicGeometry.AlgebraicSpace
