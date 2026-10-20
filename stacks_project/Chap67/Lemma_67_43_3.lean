module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.SeparatedUniversallyClosed
import StacksCheckRecall

/-!
# Valuative criterion for separated universally closed morphisms

A quasi-compact quasi-separated morphism of algebraic spaces is separated and
universally closed if and only if it satisfies the valuative criterion, if and
only if every solid valuative square admits a unique dotted lift.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.43.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Then the following are
equivalent: `f` is separated and universally closed; the valuative criterion
holds as in Definition 67.41.1 (`ValuativeCriterion`); and given any
commutative solid diagram `Spec(K) ⟶ X` over `Spec(A) ⟶ Y` where `A` is a
valuation ring with field of fractions `K`, there exists a unique dotted arrow
`Spec(A) ⟶ X`, i.e., `f` satisfies the valuative criterion as in Schemes,
Definition 26.20.3. -/
@[stacks 0A3Z] #check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.separatedUniversallyClosed_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    List.TFAE [Separated f ∧ UniversallyClosed f, ValuativeCriterion f,
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct])

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.iff_separated_universallyClosed :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f],
    Separated f ∧ UniversallyClosed f ↔ ValuativeCriterion f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.iff_uniqueLift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f],
    ValuativeCriterion f ↔
      ∀ sq : ValuativeCommSq f, sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.uniqueLift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [QuasiCompact f] [QuasiSeparated f] [ValuativeCriterion f]
    (sq : ValuativeCommSq f),
    sq.commSq.HasLift ∧ Subsingleton sq.commSq.LiftStruct)

end AlgebraicGeometry.AlgebraicSpace
