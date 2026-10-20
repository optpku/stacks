/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Integral
import StacksCheckRecall

/-!
# Integrality in the good setup

In Situation 82.2.1, a good algebraic space over a quasi-separated base is
integral exactly when it is reduced and irreducible, and each point is the
generic point of a unique integral closed subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Remark 82.2.3: the good hypotheses in Situation 82.2.1 ensure that `X` is
decent. Both assertions hold for every decent algebraic space: integrality is
equivalent to reducedness and irreducibility, and each point is the generic
point of a unique integral closed subspace. Here `IsIrreducible X` expresses
irreducibility of `|X|`, and uniqueness is a unique morphism over `X`. -/
@[stacks 0EDV] #check
  (AlgebraicGeometry.AlgebraicSpace.isIntegral_iff_isReduced_and_isIrreducible :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X],
      IsIntegral X ↔ IsReduced X ∧ IsIrreducible X)

#check
  (AlgebraicGeometry.AlgebraicSpace.existsUnique_integralClosedSubspace :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (ξ : Points X),
      ∃ Z : ClosedSubspace X,
        IsIntegral Z.X ∧
          IsGenericPoint ξ Z.pointsSet ∧
            ∀ (Z' : ClosedSubspace X),
              IsIntegral Z'.X →
                IsGenericPoint ξ Z'.pointsSet →
                  ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι)
