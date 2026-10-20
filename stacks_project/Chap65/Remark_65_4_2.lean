module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Remark 65.4.2: the listed scheme-morphism properties are stable under composition. -/
@[stacks 02WG] #check
  (AlgebraicGeometry.Scheme.Hom.composition_properties :
    ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
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
      (UniversalHomeomorphism f → UniversalHomeomorphism g → UniversalHomeomorphism (f ≫ g)))
