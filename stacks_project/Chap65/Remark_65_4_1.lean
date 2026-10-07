module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty

universe u

/- Remark 65.4.1: these morphism properties of schemes are stable under arbitrary base change. -/

/- Remark 65.4.1 (1): closed, open, and locally closed immersions. -/
@[stacks 02WF] #check IsImmersion.isStableUnderBaseChange
@[stacks 02WF] #check IsClosedImmersion.isStableUnderBaseChange
@[stacks 02WF] #check isOpenImmersion_stableUnderBaseChange

/- Remark 65.4.1 (2): quasi-compact morphisms. -/
@[stacks 02WF] #check quasiCompact_isStableUnderBaseChange

/- Remark 65.4.1 (3): universally closed morphisms. -/
@[stacks 02WF] #check universallyClosed_isStableUnderBaseChange

/- Remark 65.4.1 (4): separated and quasi-separated morphisms. -/
@[stacks 02WF] #check IsSeparated.isStableUnderBaseChange
@[stacks 02WF] #check quasiSeparated_isStableUnderBaseChange

/- Remark 65.4.1 (5): monomorphisms. -/
@[stacks 02WF] #check
  (inferInstance : (monomorphisms Scheme.{u}).IsStableUnderBaseChange)

/- Remark 65.4.1 (6): surjective morphisms. -/
@[stacks 02WF] #check
  (inferInstance : IsStableUnderBaseChange (@Surjective : MorphismProperty Scheme.{u}))

/- Remark 65.4.1 (7): universally injective morphisms. -/
@[stacks 02WF] #check UniversallyInjective.isStableUnderBaseChange

/- Remark 65.4.1 (8): affine morphisms. -/
@[stacks 02WF] #check isAffineHom_isStableUnderBaseChange

/- Remark 65.4.1 (9): quasi-affine morphisms. -/
@[stacks 02WF] #check
  (QuasiAffineHom.baseChange :
    ∀ {X S S' : Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S),
      QuasiAffineHom f → QuasiAffineHom (pullback.snd f g))

/- Remark 65.4.1 (10): locally of finite type, and of finite type. -/
@[stacks 02WF] #check locallyOfFiniteType_isStableUnderBaseChange
@[stacks 02WF] #check Scheme.Hom.finiteType_isStableUnderBaseChange

/- Remark 65.4.1 (11): locally quasi-finite, and quasi-finite. -/
@[stacks 02WF] #check
  (inferInstance :
    IsStableUnderBaseChange
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}))
@[stacks 02WF] #check Scheme.Hom.quasiFinite_isStableUnderBaseChange

/- Remark 65.4.1 (12): locally of finite presentation, and of finite presentation. -/
@[stacks 02WF] #check locallyOfFinitePresentation_isStableUnderBaseChange
@[stacks 02WF] #check Scheme.Hom.finitePresentation_isStableUnderBaseChange

/- Remark 65.4.1 (13): locally of finite type of relative dimension d. -/
@[stacks 02WF] #check
  (Scheme.Hom.instRelativeDimensionIsStableUnderBaseChange :
    ∀ d : ℕ, IsStableUnderBaseChange
      (fun (_ _ : Scheme.{u}) f ↦ Scheme.Hom.RelativeDimension f d))

/- Remark 65.4.1 (14): universally open morphisms. -/
@[stacks 02WF] #check
  (inferInstance : IsStableUnderBaseChange (@UniversallyOpen : MorphismProperty Scheme.{u}))

/- Remark 65.4.1 (15): flat morphisms. -/
@[stacks 02WF] #check Flat.isStableUnderBaseChange

/- Remark 65.4.1 (16): syntomic morphisms. -/
@[stacks 02WF] #check instSyntomicIsStableUnderBaseChange

/- Remark 65.4.1 (17): smooth morphisms. -/
@[stacks 02WF] #check smooth_isStableUnderBaseChange

/- Remark 65.4.1 (18): unramified and G-unramified morphisms. -/
@[stacks 02WF] #check unramified_isStableUnderBaseChange
@[stacks 02WF] #check gUnramified_isStableUnderBaseChange

/- Remark 65.4.1 (19): étale morphisms. -/
@[stacks 02WF] #check Etale.etale_isStableUnderBaseChange

/- Remark 65.4.1 (20): proper morphisms. -/
@[stacks 02WF] #check IsProper.isStableUnderBaseChange

/- Remark 65.4.1 (21): H-projective morphisms. -/
@[stacks 02WF] #check hProjective_isStableUnderBaseChange

/- Remark 65.4.1 (22): projective and locally projective morphisms. -/
@[stacks 02WF] #check projective_isStableUnderBaseChange
@[stacks 02WF] #check locallyProjective_isStableUnderBaseChange

/- Remark 65.4.1 (23): finite or integral morphisms. -/
@[stacks 02WF] #check
  (inferInstance : IsStableUnderBaseChange (@IsFinite : MorphismProperty Scheme.{u}))
@[stacks 02WF] #check
  (inferInstance : IsStableUnderBaseChange (@IsIntegralHom : MorphismProperty Scheme.{u}))

/- Remark 65.4.1 (24): finite locally free morphisms. -/
@[stacks 02WF] #check finiteLocallyFree_isStableUnderBaseChange

/- Remark 65.4.1 (25): universally submersive morphisms. -/
@[stacks 02WF] #check universallySubmersive_isStableUnderBaseChange

/- Remark 65.4.1 (26): universal homeomorphisms. -/
@[stacks 02WF] #check universalHomeomorphism_isStableUnderBaseChange
