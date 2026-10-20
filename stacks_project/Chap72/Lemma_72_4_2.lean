module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.GenericPoint
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 72.4.2: Let `S` be a scheme. Let `X` be an integral algebraic space over `S`.
Let `η` be the generic point of `|X|`. There are canonical identifications
`R(X) = O_{X,η}^h = κ(η)`, realized as ring equivalences
`RationalFunction X ≃+* henselianLocalRing X η ≃+* ULift (X.residueField η)`
for `η ∈ genericPoints X`, where `RationalFunction X` is the ring of rational
functions, `X.residueField η` is the residue field, and `henselianLocalRing X η`
is the henselian local ring at `η`. In particular, these rings are fields. -/
@[stacks 0END] #check (AlgebraicGeometry.AlgebraicSpace.rationalFunctionRingEquivHenselianLocalRing :
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
