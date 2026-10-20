/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints
import StacksCheckRecall

/-!
# Closed points of decent algebraic spaces

A closed point of a decent algebraic space is represented by a closed immersion
from the spectrum of a field, equivalently by the residue-field morphism
`X.fromSpecResidueField x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.14.6: Let `S` be a scheme and `X` a decent algebraic space over `S`.
A closed point `x ∈ |X|` is represented by a closed immersion from the spectrum
of a field. -/
@[stacks 0AHB]
#check (AlgebraicGeometry.AlgebraicSpace.isClosedImmersion_fromSpecResidueField :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
    x ∈ closedPoints (Points X) → IsClosedImmersion (X.fromSpecResidueField x))

#check (AlgebraicGeometry.AlgebraicSpace.exists_fieldValuedPoint_isClosedImmersion :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] {x : Points X},
    x ∈ closedPoints (Points X) →
      ∃ p : FieldValuedPoint X, IsClosedImmersion p.hom ∧ Points.mk p = x)
