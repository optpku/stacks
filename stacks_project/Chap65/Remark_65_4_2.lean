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
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.Operations
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Stability
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MorphismProperty

universe u

/- Remark 65.4.2: of the properties listed in Remark 65.4.1, these are also stable under compositions. -/

/- Remark 65.4.2 (1): closed, open, and locally closed immersions. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@IsImmersion : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@IsClosedImmersion : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check isOpenImmersion_isStableUnderComposition

/- Remark 65.4.2 (2): quasi-compact morphisms. -/
@[stacks 02WG] #check quasiCompact_isStableUnderComposition

/- Remark 65.4.2 (3): universally closed morphisms. -/
@[stacks 02WG] #check universallyClosed_isStableUnderComposition

/- Remark 65.4.2 (4): separated and quasi-separated morphisms. -/
@[stacks 02WG] #check IsSeparated.stableUnderComposition
@[stacks 02WG] #check quasiSeparated_isStableUnderComposition

/- Remark 65.4.2 (5): monomorphisms. -/
@[stacks 02WG] #check
  (inferInstance : (monomorphisms Scheme.{u}).IsStableUnderComposition)

/- Remark 65.4.2 (6): surjective morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@Surjective : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (7): universally injective morphisms. -/
@[stacks 02WG] #check universallyInjective_isStableUnderComposition

/- Remark 65.4.2 (8): affine morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@IsAffineHom : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (9): quasi-affine morphisms. -/
@[stacks 02WG] #check
  (QuasiAffineHom.comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      QuasiAffineHom f → QuasiAffineHom g → QuasiAffineHom (f ≫ g))

/- Remark 65.4.2 (10): locally of finite type, and of finite type. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check Scheme.Hom.finiteType_isStableUnderComposition

/- Remark 65.4.2 (11): locally quasi-finite, and quasi-finite. -/
@[stacks 02WG] #check
  (inferInstance :
    IsStableUnderComposition
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check Scheme.Hom.quasiFinite_isStableUnderComposition

/- Remark 65.4.2 (12): locally of finite presentation, and of finite presentation. -/
@[stacks 02WG] #check
  (inferInstance :
    IsStableUnderComposition (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check Scheme.Hom.finitePresentation_isStableUnderComposition

/- Remark 65.4.2 (13): universally open morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@UniversallyOpen : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (14): flat morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@Flat : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (15): syntomic morphisms. -/
@[stacks 02WG] #check instSyntomicIsStableUnderComposition

/- Remark 65.4.2 (16): smooth morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@Smooth : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (17): unramified and G-unramified morphisms. -/
@[stacks 02WG] #check
  (unramified_comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      [Unramified f] [Unramified g], Unramified (f ≫ g))
@[stacks 02WG] #check
  (gUnramified_comp :
    ∀ {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
      [GUnramified f] [GUnramified g], GUnramified (f ≫ g))

/- Remark 65.4.2 (18): étale morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@Etale : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (19): proper morphisms. -/
@[stacks 02WG] #check IsProper.stableUnderComposition

/- Remark 65.4.2 (20): H-projective morphisms. -/
@[stacks 02WG] #check hProjective_isStableUnderComposition

/- Remark 65.4.2 (21): finite or integral morphisms. -/
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@IsFinite : MorphismProperty Scheme.{u}))
@[stacks 02WG] #check
  (inferInstance : IsStableUnderComposition (@IsIntegralHom : MorphismProperty Scheme.{u}))

/- Remark 65.4.2 (22): finite locally free morphisms. -/
@[stacks 02WG] #check finiteLocallyFree_isStableUnderComposition

/- Remark 65.4.2 (23): universally submersive morphisms. -/
@[stacks 02WG] #check universallySubmersive_isStableUnderComposition

/- Remark 65.4.2 (24): universal homeomorphisms. -/
@[stacks 02WG] #check universalHomeomorphism_isStableUnderComposition
