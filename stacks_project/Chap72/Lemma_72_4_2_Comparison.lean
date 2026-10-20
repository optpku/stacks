/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import stacks_project.Chap72.Definition_72_5_2_ResidueField

/-!
# Generic-point comparison compatibility

The canonical ring comparisons are provided by their shared mathematical owners.
Generic-point existence and residue-field morphisms remain publicly available.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRingEquivHenselianLocalRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X),
    RationalFunction X ≃+* henselianLocalRing X η)

#check (AlgebraicGeometry.AlgebraicSpace.henselianLocalRingEquivResidueField :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X),
    henselianLocalRing X η ≃+* ULift.{u + 1} (X.residueField η))

#check (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRingEquivResidueField :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X),
    RationalFunction X ≃+* ULift.{u + 1} (X.residueField η))

#check (AlgebraicGeometry.AlgebraicSpace.instField_rationalFunctionRing :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X],
    Field (RationalFunction X))

#check (AlgebraicGeometry.AlgebraicSpace.field_henselianLocalRing_genericPoint :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIntegral X]
    {η : Points X} (hη : η ∈ genericPoints X),
    Field (henselianLocalRing X η))
