module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Factorization

/-!
# DVR valuative uniqueness along a morphism of algebraic spaces

A morphism of algebraic spaces satisfies the uniqueness part of the DVR
valuative criterion along a second morphism when every valuative square whose
generic arrow factors through that morphism, and whose ring is a discrete
valuation ring, has at most one dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.Uniqueness :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.uniqueness_iff :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y),
    Uniqueness h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Subsingleton sq.commSq.LiftStruct)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.uniqueness_of :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (h_uniqueness :
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → Subsingleton sq.commSq.LiftStruct),
    Uniqueness h f)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.uniqueness :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y}
    (h_uniqueness : Uniqueness h f) (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R), Subsingleton sq.commSq.LiftStruct)

#check (AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Along.uniqueness_of_dvrUniqueness :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f], Uniqueness h f)

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
