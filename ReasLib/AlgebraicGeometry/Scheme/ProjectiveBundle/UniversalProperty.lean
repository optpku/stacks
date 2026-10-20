module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Sections
public import ReasLib.AlgebraicGeometry.Scheme.ProjectiveBundle.Presentation

/-!
# Universal property of symmetric projective bundles

The pullback of the concrete tautological quotient defines the map from lifts
to invertible-quotient classes.  Representability is expressed as bijectivity
of this forward map, without storing an inverse or equivalence as input data.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveBundle

variable {X P : Scheme.{u}} {ℰ : X.Modules} [ℰ.IsQuasicoherent]

namespace QuotientFunctor

/-- The value of the invertible-quotient-class functor at a test morphism. -/
abbrev Point (ℰ : X.Modules) {T : Scheme.{u}} (f : T ⟶ X) :=
  CategoryTheory.InvertibleQuotient.IsoClass ((Scheme.Modules.pullback f).obj ℰ)

/-- Pull back an invertible-quotient class along a morphism of test schemes, with the canonical
comparison identifying successive pullback with pullback along the composite. -/
noncomputable def quotientPointMap {T R : Scheme.{u}} (f : T ⟶ X) (g : R ⟶ T) :
    Point ℰ f → Point ℰ (g ≫ f) := fun q ↦
  CategoryTheory.InvertibleQuotient.precomposeIsoClass
    ((Scheme.Modules.pullbackComp g f).app ℰ).symm
    (CategoryTheory.InvertibleQuotient.pullbackClass g q)

/-- Pullback of quotient classes along an identity test morphism is the identity after the
canonical source comparison. -/
theorem quotientPointMap_id {T : Scheme.{u}} (f : T ⟶ X) (q : Point ℰ f) :
    quotientPointMap (ℰ := ℰ) f (𝟙 T) q = q := sorry

/-- Pullback of quotient classes along a composite agrees with successive pullback. -/
theorem quotientPointMap_comp {T R S : Scheme.{u}} (f : T ⟶ X)
    (g : R ⟶ T) (h : S ⟶ R) (q : Point ℰ f) :
    quotientPointMap (ℰ := ℰ) (g ≫ f) h (quotientPointMap f g q) =
      quotientPointMap f (h ≫ g) q := sorry

end QuotientFunctor

namespace SymmetricPresentation

/-- The quotient class obtained by pulling back the concrete tautological quotient along a
lift. -/
noncomputable def liftToQuotientClass {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) :
    Lift π f → QuotientFunctor.Point ℰ f := fun σ ↦
  CategoryTheory.InvertibleQuotient.IsoClass.mk (S.liftSourceQuotient f σ)

/-- The concrete lift-to-quotient-class map is bijective for every test morphism. -/
theorem liftToQuotientClass_bijective {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) {T : Scheme.{u}} (f : T ⟶ X) :
    Function.Bijective (S.liftToQuotientClass f) := sorry

/-- The concrete lift-to-quotient-class map is natural under arbitrary precomposition. -/
theorem liftToQuotientClass_naturality {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) {T R : Scheme.{u}} (f : T ⟶ X)
    (σ : Lift π f) (g : R ⟶ T) :
    S.liftToQuotientClass (g ≫ f) (σ.precomp g) =
      QuotientFunctor.quotientPointMap f g (S.liftToQuotientClass f σ) := sorry

/-- The quotient class associated to a section, transported through identity pullback. -/
noncomputable def sectionToQuotientClass {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    Lift π (𝟙 X) → CategoryTheory.InvertibleQuotient.IsoClass ℰ := fun σ ↦
  CategoryTheory.InvertibleQuotient.isoClassEquivOfIso
    ((Scheme.Modules.pullbackId X).app ℰ) (S.liftToQuotientClass (𝟙 X) σ)

/-- Sections of a symmetric projective bundle correspond bijectively to invertible quotient
classes of the module being projectivized. -/
theorem sectionToQuotientClass_bijective {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) :
    Function.Bijective S.sectionToQuotientClass := sorry

/-- The structure morphism in a symmetric projective-bundle presentation is separated. -/
theorem isSeparated {π : P ⟶ X} (S : SymmetricPresentation π ℰ) :
    IsSeparated π := sorry

/-- Every section of a symmetric projective-bundle presentation is a closed immersion. -/
theorem section_isClosedImmersion {π : P ⟶ X} (S : SymmetricPresentation π ℰ)
    (σ : Lift π (𝟙 X)) : IsClosedImmersion σ.hom := sorry

/-- The concrete quotient of a lift is obtained by source transport of the pulled-back
tautological quotient. -/
theorem liftQuotient_localCoordinates {π : P ⟶ X}
    (S : SymmetricPresentation π ℰ) {T : Scheme.{u}} (f : T ⟶ X)
    (σ : Lift π f) :
    (S.liftSourceQuotient f σ).hom =
      (Lift.pullbackSourceIso σ ℰ).inv ≫
        (Scheme.Modules.pullback σ.hom).map S.tautologicalMap := sorry

end SymmetricPresentation

end AlgebraicGeometry.Scheme.ProjectiveBundle
