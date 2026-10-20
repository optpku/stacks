/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

/-!
# Valuative criterion for universal closedness of separated morphisms

A quasi-compact separated morphism of algebraic spaces is universally closed if
and only if it satisfies the existence part of the valuative criterion, if and
only if every solid valuative square admits a dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyClosed

/- Lemma 67.42.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
separated morphism of algebraic spaces over `S`. Then the following are
equivalent: `UniversallyClosed f`; the existence part of the valuative
criterion holds as in Definition 67.41.1 (`ValuativeCriterion.Existence`); and
given any commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where `A`
is a valuation ring with field of fractions `K`, there exists a dotted arrow
`Spec(A) ⟶ X`, i.e., `f` satisfies the existence part of the valuative
criterion as in Schemes, Definition 26.20.3. -/
@[stacks 0A3Y]
#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.existence_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Separated f],
    List.TFAE [UniversallyClosed f, ValuativeCriterion.Existence f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift])

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.iff_hasLift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [Separated f],
    UniversallyClosed f ↔ ∀ sq : ValuativeCommSq f, sq.commSq.HasLift)

#check (AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.hasLift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
      [QuasiCompact f] [Separated f] [UniversallyClosed f] (sq : ValuativeCommSq f),
    sq.commSq.HasLift)

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
