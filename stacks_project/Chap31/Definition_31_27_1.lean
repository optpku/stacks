module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing.MeromorphicSection
import StacksCheckRecall

/-!
# Definition 31.27.1

The order of vanishing of a meromorphic section along a prime divisor.

@stack 02SF
-/

@[expose] public section

universe u

/- Definition 31.27.1: For an invertible module on a locally Noetherian integral scheme, the
order of a regular meromorphic section along a prime divisor is the order of its quotient by a
generator in the generic-point stalk. -/
@[stacks 02SF] #check
  (AlgebraicGeometry.Scheme.regularMeromorphicSectionOrderAlongPrimeDivisor :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsIntegral X] {L : X.Modules}
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      (s : X.toLocallyRingedSpace.meromorphicSections L)
      (hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection L s)
      (Z : AlgebraicGeometry.PrimeDivisor X), ℤ)

#check
  (AlgebraicGeometry.Scheme.regularMeromorphicSectionOrderAlongPrimeDivisor_eq_localOrder :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsIntegral X] {L : X.Modules}
      [AlgebraicGeometry.Scheme.Modules.Invertible L]
      {s : X.toLocallyRingedSpace.meromorphicSections L}
      {Z : AlgebraicGeometry.PrimeDivisor X}
      {hs : X.toLocallyRingedSpace.IsRegularMeromorphicSection L s}
      (data : AlgebraicGeometry.Scheme.RegularMeromorphicSectionOrderPresentation L s hs Z),
      AlgebraicGeometry.Scheme.regularMeromorphicSectionOrderAlongPrimeDivisor s hs Z =
        -- Local instance justification (defeq pin): the complete theorem type must install the
        -- canonical prime-divisor dimension bound used by `Ring.ordFrac`.
        letI : Ring.KrullDimLE 1 Z.genericPointStalk :=
          (AlgebraicGeometry.Scheme.PrimeDivisorOrderPresentation.ofPrimeDivisor
            (ℒ := L) (s := s) Z data.quotient).krullDimLE
        WithZero.log (Ring.ordFrac Z.genericPointStalk
          (data.quotient : FractionRing Z.genericPointStalk)))
