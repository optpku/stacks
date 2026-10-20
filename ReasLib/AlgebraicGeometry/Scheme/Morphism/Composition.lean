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

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Composition preserves closed, open, and locally closed immersions, quasi-compactness,
universal closedness, separation, quasi-separation, monomorphisms, surjectivity,
universal injectivity, affine and quasi-affine morphisms, local and global finite type,
local and global quasi-finiteness, local and global finite presentation, universal openness,
flatness, syntomic and smooth morphisms, unramified and G-unramified morphisms,
étale and proper morphisms, H-projective morphisms, finite and integral morphisms,
finite local freeness, universal submersiveness, and universal homeomorphisms. -/
theorem composition_properties {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (IsClosedImmersion f → IsClosedImmersion g → IsClosedImmersion (f ≫ g)) ∧
    (IsOpenImmersion f → IsOpenImmersion g → IsOpenImmersion (f ≫ g)) ∧
    (IsImmersion f → IsImmersion g → IsImmersion (f ≫ g)) ∧
    (QuasiCompact f → QuasiCompact g → QuasiCompact (f ≫ g)) ∧
    (UniversallyClosed f → UniversallyClosed g → UniversallyClosed (f ≫ g)) ∧
    (IsSeparated f → IsSeparated g → IsSeparated (f ≫ g)) ∧
    (QuasiSeparated f → QuasiSeparated g → QuasiSeparated (f ≫ g)) ∧
    (Mono f → Mono g → Mono (f ≫ g)) ∧
    (Surjective f → Surjective g → Surjective (f ≫ g)) ∧
    (UniversallyInjective f → UniversallyInjective g → UniversallyInjective (f ≫ g)) ∧
    (IsAffineHom f → IsAffineHom g → IsAffineHom (f ≫ g)) ∧
    (QuasiAffineHom f → QuasiAffineHom g → QuasiAffineHom (f ≫ g)) ∧
    (LocallyOfFiniteType f → LocallyOfFiniteType g → LocallyOfFiniteType (f ≫ g)) ∧
    (Scheme.Hom.FiniteType f → Scheme.Hom.FiniteType g → Scheme.Hom.FiniteType (f ≫ g)) ∧
    (LocallyOfFiniteType f ∧ LocallyQuasiFinite f →
      LocallyOfFiniteType g ∧ LocallyQuasiFinite g →
      LocallyOfFiniteType (f ≫ g) ∧ LocallyQuasiFinite (f ≫ g)) ∧
    (Scheme.Hom.QuasiFinite f → Scheme.Hom.QuasiFinite g → Scheme.Hom.QuasiFinite (f ≫ g)) ∧
    (LocallyOfFinitePresentation f → LocallyOfFinitePresentation g →
      LocallyOfFinitePresentation (f ≫ g)) ∧
    (Scheme.Hom.FinitePresentation f → Scheme.Hom.FinitePresentation g →
      Scheme.Hom.FinitePresentation (f ≫ g)) ∧
    (UniversallyOpen f → UniversallyOpen g → UniversallyOpen (f ≫ g)) ∧
    (Flat f → Flat g → Flat (f ≫ g)) ∧
    (Syntomic f → Syntomic g → Syntomic (f ≫ g)) ∧
    (Smooth f → Smooth g → Smooth (f ≫ g)) ∧
    (Unramified f → Unramified g → Unramified (f ≫ g)) ∧
    (GUnramified f → GUnramified g → GUnramified (f ≫ g)) ∧
    (Etale f → Etale g → Etale (f ≫ g)) ∧
    (IsProper f → IsProper g → IsProper (f ≫ g)) ∧
    (HProjective f → HProjective g → HProjective (f ≫ g)) ∧
    (IsFinite f → IsFinite g → IsFinite (f ≫ g)) ∧
    (IsIntegralHom f → IsIntegralHom g → IsIntegralHom (f ≫ g)) ∧
    (IsFiniteLocallyFree f → IsFiniteLocallyFree g → IsFiniteLocallyFree (f ≫ g)) ∧
    (UniversallySubmersive f → UniversallySubmersive g → UniversallySubmersive (f ≫ g)) ∧
    (UniversalHomeomorphism f → UniversalHomeomorphism g → UniversalHomeomorphism (f ≫ g)) := sorry

end AlgebraicGeometry.Scheme.Hom
