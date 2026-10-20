/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Factorization

/-!
# DVR valuative existence along a morphism of algebraic spaces

The shared factored-DVR API supplies existence of dotted lifts over the original
DVR for squares whose generic arrow factors through a fixed morphism.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (ValuativeCriterion.DVR.Along.Existence :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y), Prop)

#check (ValuativeCriterion.DVR.Along.existence_iff :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y),
    ValuativeCriterion.DVR.Along.Existence h f ↔
      ∀ sq : ValuativeCommSqFactorsThrough h f,
        IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift)

#check (ValuativeCriterion.DVR.Along.of :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y},
    (∀ sq : ValuativeCommSqFactorsThrough h f,
      IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift) →
    ValuativeCriterion.DVR.Along.Existence h f)

#check (ValuativeCriterion.DVR.Along.existence :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} {h : U ⟶ X} {f : X ⟶ Y},
    ValuativeCriterion.DVR.Along.Existence h f →
    ∀ sq : ValuativeCommSqFactorsThrough h f,
      IsDiscreteValuationRing sq.sq.R → sq.commSq.HasLift)

#check (ValuativeCriterion.DVR.Along.existence_of_dvrExistence :
  ∀ {S : Scheme.{u}} {U X Y : AlgebraicSpace S} (h : U ⟶ X) (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Existence f], ValuativeCriterion.DVR.Along.Existence h f)

end AlgebraicGeometry.AlgebraicSpace
