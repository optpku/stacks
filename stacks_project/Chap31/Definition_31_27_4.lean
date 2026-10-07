module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
import StacksCheckRecall

/-!
# Definition 31.27.4

The Weil divisor and divisor class associated to a meromorphic section of an invertible module.

@stack 0BE6
-/

@[expose] public section

open AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff_def :
  ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0)
    (Z : PrimeDivisor X),
    AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z =
      AlgebraicGeometry.Scheme.regularMeromorphicSectionOrderAlongPrimeDivisor s
        ((AlgebraicGeometry.isRegularMeromorphicSection_iff_ne_zero L s).2 hs) Z)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0),
    WeilDivisor X)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor_coeff :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0)
    (Z : PrimeDivisor X),
    (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor X L s hs).coeff Z =
      AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorCoeff L s hs Z)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0),
    WeilDivisorClassGroup X)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass_def :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0),
    AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass X L s hs =
      weilDivisorClassGroupMk X
        (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor X L s hs))

#check (AlgebraicGeometry.Scheme.invertibleModuleWeilDivisorClass :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
    WeilDivisorClassGroup X)

/- Definition 31.27.4: the canonical divisor class associated to an invertible module is
computed from any nonzero meromorphic section. -/
@[stacks 0BE6] #check (AlgebraicGeometry.Scheme.invertibleModuleWeilDivisorClass_eq :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s : X.toLocallyRingedSpace.meromorphicSections L) (hs : s ≠ 0),
    AlgebraicGeometry.Scheme.invertibleModuleWeilDivisorClass X L =
      AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass X L s hs)

#check (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass_eq :
  ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
    (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L]
    (s t : X.toLocallyRingedSpace.meromorphicSections L)
    (hs : s ≠ 0) (ht : t ≠ 0),
    AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass X L s hs =
      AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisorClass X L t ht)
