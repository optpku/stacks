module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.QuasiIso
public import ReasLib.CategoryTheory.Localization.Lifting.Computation
import Mathlib.Tactic.CrossRefAttribute

/-!
# The derived ideal-sheaf eta functor

Complexes with degreewise monic ideal action form a localization model for the derived category.
The eta functor sends quasi-isomorphisms in this model to isomorphisms after localization, so the
standard localization lift constructs the derived eta functor together with one natural comparison
isomorphism controlling both objects and morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived

variable {X : RingedSpace.{u}}
variable (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))

/-- The inclusion of the canonical eta domain into all cochain complexes. -/
abbrev domainInclusion : Domain I ⥤ CochainComplex X.Modules ℤ :=
  (IsActionMono.complex I (up ℤ)).ι

/-- Quasi-isomorphisms in the canonical eta domain. -/
abbrev quasiIso : MorphismProperty (Domain I) :=
  (HomologicalComplex.quasiIso X.Modules (up ℤ)).inverseImage (domainInclusion I)

/-- The canonical functor from the eta domain to the derived category. -/
abbrev toDerived : Domain I ⥤ DerivedCategory X.Modules :=
  domainInclusion I ⋙ DerivedCategory.Q

/-- Complexes with degreewise monic `I`-action form a localization model for the derived category.
This packages the reusable resolution statement needed to derive functors from the eta domain. -/
@[stacks 0F8Q "action-monic localization", instance]
theorem toDerived_isLocalization : (toDerived I).IsLocalization (quasiIso I) := sorry

section Invertible

variable [isInvertibleObject (I : X.Modules)]

/-- The underived eta functor followed by the localization to the derived category. -/
abbrev model : Domain I ⥤ DerivedCategory X.Modules :=
  Eta.functor I ⋙ DerivedCategory.Q

/-- The localized underived eta model inverts quasi-isomorphisms in its canonical domain. -/
theorem model_inverts : (quasiIso I).IsInvertedBy (model I) := sorry

/-- Lemma 20.55.7 (0F8Q): the additive derived Berthelot-Ogus eta endofunctor.  It is the
localization lift of the eta construction on complexes with degreewise monic ideal action. -/
@[stacks 0F8Q]
noncomputable def functor :
    DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  Localization.lift (model I) (model_inverts I) (toDerived I)

/-- The derived eta functor is additive. -/
@[stacks 0F8Q "additivity", instance]
theorem additive : (functor I).Additive := sorry

/-- The natural comparison computing the derived eta functor on its canonical domain.  Its
naturality is the single coherent owner of the object and morphism computation rules. -/
@[stacks 0F8Q "derived eta comparison"]
noncomputable def comparison : toDerived I ⋙ functor I ≅ model I :=
  Localization.fac (model I) (model_inverts I) (toDerived I)

/-- The component of the derived eta comparison at an action-monic complex. -/
noncomputable def comparisonApp (K : Domain I) :
    (functor I).obj ((toDerived I).obj K) ≅
      DerivedCategory.Q.obj ((Eta.functor I).obj K) :=
  (comparison I).app K

/-- Naturality of the derived eta comparison gives the computation rule on morphisms. -/
@[reassoc]
theorem comparison_naturality {K L : Domain I} (φ : K ⟶ L) :
    (functor I).map ((toDerived I).map φ) ≫ (comparison I).hom.app L =
      (comparison I).hom.app K ≫ (model I).map φ := sorry

/-- The derived eta functor maps a localized morphism by conjugating the underived eta map with
the canonical comparison isomorphisms. -/
theorem map_toDerived {K L : Domain I} (φ : K ⟶ L) :
    (functor I).map ((toDerived I).map φ) =
      (comparison I).hom.app K ≫ (model I).map φ ≫ (comparison I).inv.app L := sorry

end Invertible

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta.Derived
