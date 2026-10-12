/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded.Homotopy.Derived
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.FunctorialResolution
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Replacement

/-!
# K-injective localization over an explicit base ring

The K-injective resolution model is independent of the scalar presentation of a cochain complex,
but its homotopy category remembers the chosen `R`-linear enrichment.  This leaf exposes that
model and its localization once, for arbitrary commutative `R`.
-/

@[expose] public section

noncomputable section

universe r u v w g

open CategoryTheory
open CategoryTheory.Limits
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open scoped CategoryTheory.CochainComplex.Enriched.Over

namespace CategoryTheory.CochainComplex.Enriched.Over.KInjective

variable {R : Type r} [CommRing R]
variable {C : Type u} [Category.{v} C] [Abelian C] [Linear R C]

/-- K-injective objects in the explicit `R`-linear cochain homotopy category. -/
@[stacks 0CS6 "K-injective objects over an explicit base ring"]
def property : ObjectProperty (DifferentialGradedCategory.K R (CochainComplex C ℤ)) :=
  fun K => K.obj.IsKInjective

/-- Membership in the explicit-base-ring K-injective subcategory is strict K-injectivity. -/
@[simp]
theorem property_iff (K : DifferentialGradedCategory.K R (CochainComplex C ℤ)) :
    property (R := R) K ↔ K.obj.IsKInjective := sorry

/-- A full-subcategory object carries its K-injectivity proof as an instance. -/
@[stacks 0CS6 "explicit-base-ring K-injective model instance"]
instance fullSubcategoryIsKInjective
    (I : (property (R := R) (C := C)).FullSubcategory) : I.obj.obj.IsKInjective := sorry

/-- Quasi-isomorphisms restricted to explicit-base-ring K-injective objects. -/
@[stacks 0CS6 "explicit-base-ring K-injective denominators"]
abbrev qis : MorphismProperty (property (R := R) (C := C)).FullSubcategory :=
  fullSubcategoryLocalizationSystem (property (R := R) (C := C))
    (CochainComplex.Enriched.Over.quasiIso (R := R) (A := C))

/-- The localization from explicit-base-ring K-injective objects to the derived category. -/
@[stacks 0CS6 "explicit-base-ring K-injective localization"]
noncomputable abbrev localization [HasDerivedCategory.{w} C] :
    (property (R := R) (C := C)).FullSubcategory ⥤ DerivedCategory.{w} C :=
  (property (R := R) (C := C)).ι ⋙
    CochainComplex.Enriched.Over.derivedQ (R := R) (A := C)

/-- The K-injective localization presents the usual derived category in a Grothendieck category. -/
@[stacks 0CS6 "explicit-base-ring K-injective derived localization"]
noncomputable instance localizationIsLocalization [HasDerivedCategory.{w} C]
    [IsGrothendieckAbelian.{g} C] :
    (localization (R := R) (C := C)).IsLocalization (qis (R := R) (C := C)) := sorry

/-- The K-injective object produced by a functorial resolution. -/
@[stacks 090Y "explicit-base-ring functorial K-injective resolution object"]
noncomputable def resolutionObject
    (J : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K R (CochainComplex C ℤ)) :
    (property (R := R) (C := C)).FullSubcategory :=
  ⟨⟨(J.resolution X.obj).complex⟩, (J.resolution X.obj).isKInjective⟩

/-- The homotopy-class arrow from a complex to its functorial K-injective resolution. -/
@[stacks 090Y "explicit-base-ring functorial K-injective resolution arrow"]
noncomputable def resolutionMap
    (J : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K R (CochainComplex C ℤ)) :
    X ⟶ (property (R := R) (C := C)).ι.obj (resolutionObject (R := R) J X) :=
  @DifferentialGradedCategory.CompHom.toHomotopyClass R _ _
    (CochainComplex.differentialGradedCategory C R) _ _
    (CochainComplex.Enriched.Over.ofHom (R := R) (J.resolution X.obj).ι)

/-- A functorial K-injective resolution supplies a right denominator resolution. -/
@[stacks 090Y "explicit-base-ring K-injective right resolution"]
noncomputable def rightResolutionOf
    (J : CochainComplex.KInjectiveResolution.Functorial C)
    (X : DifferentialGradedCategory.K R (CochainComplex C ℤ)) :
    (fullSubcategoryLocalizerMorphism (property (R := R) (C := C))
      (CochainComplex.Enriched.Over.quasiIso (R := R) (A := C))).RightResolution X :=
  { X₁ := resolutionObject (R := R) J X
    w := resolutionMap (R := R) J X
    hw := sorry }

/-- Grothendieck abelian categories admit right denominator resolutions by K-injectives. -/
@[stacks 090Y "explicit-base-ring K-injective right-resolution cover"]
noncomputable instance hasRightResolutions_of_grothendieck
    [IsGrothendieckAbelian.{g} C] :
    (fullSubcategoryLocalizerMorphism (property (R := R) (C := C))
      (CochainComplex.Enriched.Over.quasiIso (R := R) (A := C))).HasRightResolutions := sorry

/-- The explicit-base-ring K-injective inclusion is a localized equivalence. -/
@[stacks 0CS6 "explicit-base-ring K-injective localized equivalence"]
instance localizerIsLocalizedEquivalence [IsGrothendieckAbelian.{g} C] :
    (fullSubcategoryLocalizerMorphism (property (R := R) (C := C))
      (CochainComplex.Enriched.Over.quasiIso (R := R) (A := C))).IsLocalizedEquivalence := sorry

end CategoryTheory.CochainComplex.Enriched.Over.KInjective
