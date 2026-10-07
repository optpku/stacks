module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.ClosedImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Monomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiAffine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompact
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiCompactImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiFinite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Separated
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Smooth
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Surjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Syntomic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyClosed
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyInjective
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.UniversallySubmersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Unramified
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty

universe u

/- Of the properties in Remark 65.4.1 that are stable under base change, the
following are fpqc local on the base (and a fortiori fppf local on the base). -/

/- Remark 65.4.3 (1): closed, open, and quasi-compact immersions. -/
@[stacks 02WH] #check
  (IsClosedImmersion.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsClosedImmersion : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (IsOpenImmersion.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsOpenImmersion : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (QuasiCompactImmersion.isLocalAtTargetFpqc :
    IsLocalAtTarget
      ((@QuasiCompact ⊓ @IsImmersion) : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (2): quasi-compact morphisms. -/
@[stacks 02WH] #check
  (QuasiCompact.isLocalAtTargetFpqc :
    IsLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (3): universally closed morphisms. -/
@[stacks 02WH] #check
  (UniversallyClosed.isLocalAtTargetFpqc :
    IsLocalAtTarget (@UniversallyClosed : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (4): separated and quasi-separated morphisms. -/
@[stacks 02WH] #check
  (QuasiSeparated.isLocalAtTargetFpqc :
    IsLocalAtTarget (@QuasiSeparated : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (IsSeparated.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsSeparated : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (5): monomorphisms. -/
@[stacks 02WH] #check
  (Monomorphisms.isLocalAtTargetFpqc :
    IsLocalAtTarget (monomorphisms Scheme.{u}) Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (6): surjective morphisms. -/
@[stacks 02WH] #check
  (Surjective.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Surjective : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (7): universally injective morphisms. -/
@[stacks 02WH] #check
  (UniversallyInjective.isLocalAtTargetFpqc :
    IsLocalAtTarget (@UniversallyInjective : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (8): affine morphisms. -/
@[stacks 02WH] #check
  (IsAffineHom.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (9): quasi-affine morphisms. -/
@[stacks 02WH] #check
  (QuasiAffineHom.isLocalAtTargetFpqc :
    IsLocalAtTarget (@QuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (10): locally of finite type, and of finite type. -/
@[stacks 02WH] #check
  (LocallyOfFiniteType.isLocalAtTargetFpqc :
    IsLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (Scheme.Hom.FiniteType.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Scheme.Hom.FiniteType : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (11): locally quasi-finite, and quasi-finite. -/
@[stacks 02WH] #check
  (Scheme.Hom.FiniteType.locallyQuasiFinite_isLocalAtTargetFpqc :
    IsLocalAtTarget
      ((@LocallyOfFiniteType ⊓ @LocallyQuasiFinite) :
        MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (Scheme.Hom.QuasiFinite.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Scheme.Hom.QuasiFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (12): locally of finite presentation, and of finite presentation. -/
@[stacks 02WH] #check
  (LocallyOfFinitePresentation.isLocalAtTargetFpqc :
    IsLocalAtTarget
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (Scheme.Hom.FinitePresentation.isLocalAtTargetFpqc :
    IsLocalAtTarget
      (@Scheme.Hom.FinitePresentation : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (13): locally of finite type of relative dimension d. -/
@[stacks 02WH] #check
  (Scheme.Hom.RelativeDimension.isLocalAtTargetFpqc :
    ∀ d : ℕ,
      IsLocalAtTarget
        ((fun _ _ f ↦ Scheme.Hom.RelativeDimension f d) :
          MorphismProperty Scheme.{u})
        Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (14): universally open morphisms. -/
@[stacks 02WH] #check
  (UniversallyOpen.isLocalAtTargetFpqc :
    IsLocalAtTarget (@UniversallyOpen : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (15): flat morphisms. -/
@[stacks 02WH] #check
  (Flat.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Flat : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (16): syntomic morphisms. -/
@[stacks 02WH] #check
  (Syntomic.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Syntomic : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (17): smooth morphisms. -/
@[stacks 02WH] #check
  (Smooth.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Smooth : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (18): unramified and G-unramified morphisms. -/
@[stacks 02WH] #check
  (Unramified.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Unramified : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (GUnramified.isLocalAtTargetFpqc :
    IsLocalAtTarget (@GUnramified : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (19): étale morphisms. -/
@[stacks 02WH] #check
  (Etale.isLocalAtTargetFpqc :
    IsLocalAtTarget (@Etale : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (20): proper morphisms. -/
@[stacks 02WH] #check
  (IsProper.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsProper : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (21): finite or integral morphisms. -/
@[stacks 02WH] #check
  (IsFinite.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)
@[stacks 02WH] #check
  (IsIntegralHom.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsIntegralHom : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (22): finite locally free morphisms. -/
@[stacks 02WH] #check
  (IsFiniteLocallyFree.isLocalAtTargetFpqc :
    IsLocalAtTarget (@IsFiniteLocallyFree : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (23): universally submersive morphisms. -/
@[stacks 02WH] #check
  (UniversallySubmersive.isLocalAtTargetFpqc :
    IsLocalAtTarget (@UniversallySubmersive : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (24): universal homeomorphisms. -/
@[stacks 02WH] #check
  (UniversalHomeomorphism.isLocalAtTargetFpqc :
    IsLocalAtTarget (@UniversalHomeomorphism : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage)

/- Remark 65.4.3 (25): a general immersion may fail to be fpqc local on the base,
but is fppf local on the base. -/
@[stacks 02WH] #check
  (IsImmersion.isLocalAtTargetFppf :
    IsLocalAtTarget (@IsImmersion : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage)
