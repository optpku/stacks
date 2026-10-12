/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FormalNeighborhood.ExceptionalCurve

import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.FormalNeighborhood

variable {X : Scheme.{u}} [IsNoetherian X]
variable (E : X.IdealSheafData) [AlgebraicGeometry.IsExceptionalCurveFirstKind E]

/- Lemma 54.16.3 (1): the inverse limit of the section rings of the positive infinitesimal
neighborhoods of an exceptional curve of the first kind is a regular local ring. -/
@[stacks 0C2K] #check
  (AlgebraicGeometry.Scheme.FormalNeighborhood.instIsRegularLocalRing :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
      [AlgebraicGeometry.IsExceptionalCurveFirstKind E],
      IsRegularLocalRing (AlgebraicGeometry.Scheme.FormalNeighborhood.ring E))

/- Lemma 54.16.3 (2): the formal-neighborhood ring of an exceptional curve of the first kind
is a complete local ring. -/
@[stacks 0C2K] #check
  (AlgebraicGeometry.Scheme.FormalNeighborhood.instIsCompleteLocalRing :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
      [AlgebraicGeometry.IsExceptionalCurveFirstKind E],
      IsCompleteLocalRing (AlgebraicGeometry.Scheme.FormalNeighborhood.ring E))

/- Lemma 54.16.3 (3): the formal-neighborhood ring of an exceptional curve of the first kind
has Krull dimension two. -/
@[stacks 0C2K] #check
  (AlgebraicGeometry.Scheme.FormalNeighborhood.ringKrullDim_eq_two :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
      [AlgebraicGeometry.IsExceptionalCurveFirstKind E],
      ringKrullDim (AlgebraicGeometry.Scheme.FormalNeighborhood.ring E) = 2)

/- Lemma 54.16.3 (4): the kernel of the projection to positive stage `n` is the `(n + 1)`st
power of the maximal ideal. -/
@[stacks 0C2K] #check
  (AlgebraicGeometry.Scheme.FormalNeighborhood.ker_projection :
    ∀ {X : Scheme.{u}} [IsNoetherian X] (E : X.IdealSheafData)
      [AlgebraicGeometry.IsExceptionalCurveFirstKind E] (n : ℕ),
      RingHom.ker (AlgebraicGeometry.Scheme.FormalNeighborhood.projection E n).hom =
        IsLocalRing.maximalIdeal (AlgebraicGeometry.Scheme.FormalNeighborhood.ring E) ^ (n + 1))

end AlgebraicGeometry.Scheme.FormalNeighborhood
