module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.SmoothProper
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.94.4: for a smooth proper morphism and a locally constant abelian étale
sheaf with prime-to-characteristic torsion geometric stalks, specialization on the
geometric stalks of the derived direct image is an isomorphism. -/
@[stacks 0GKD] #check
  (AlgebraicGeometry.Scheme.Etale.isIso_derivedPushforward_specializationMap_of_locallyConstant :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [IsProper f] (s t : GeometricPoint S)
      (point : Spec (.of t.K) ⟶ strictHenselizationAt S s)
      (point_over : point ≫ StrictHenselization.toScheme S s = t.hom)
      (F : EtaleVanishingCycles.Coefficients X) [Sheaf.IsLocallyConstant F]
      (hF : geometricStalk_isPrimeToCharTorsion F),
      IsIso (Etale.derivedPushforward_specializationMap f s t point point_over
        (etaleSheafInDegreeZero F)))
