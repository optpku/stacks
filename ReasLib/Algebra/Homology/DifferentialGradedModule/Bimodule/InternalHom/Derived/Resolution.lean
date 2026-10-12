/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.KInjective
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Resolution models for derived internal Hom

Property-(I) targets compute the fixed-source right-derived internal-Hom functor.  This file
owns the resulting comparison between a strict internal-Hom object and the abstract derived
value; cohomology and representability are deliberately left to downstream leaves.

The concrete `PropertyI` resolution route is intentionally SameCarrier: its target module,
the right algebra, and the right-module carrier of the bimodule all live in `v`.  For mixed
algebra/module carriers use the resolution-independent owners in `InternalHom.Derived` and
`InternalHom.Derived.Cohomology`; this leaf does not pretend to generalize the `PropertyI`
owner beyond its current mathematical boundary.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedBimodule.InternalHom.Derived

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, v} R}

/-- A K-injective target computes fixed-source derived internal Hom. -/
@[stacks 070Y "K-injective computation of derived internal Hom"]
theorem KInjective.computesAt (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :
    Functor.RightDerived.ComputesAt (InternalHom.derivedSourceFunctor T)
      (DifferentialGradedModule.quasiIso B)
      ((DifferentialGradedModule.toK B).obj I) := sorry

/-- A property-(I) target computes fixed-source derived internal Hom. -/
@[stacks 070Y "property-I computation of derived internal Hom"]
theorem PropertyI.computesAt (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.HasPropertyI B I) :
    Functor.RightDerived.ComputesAt (InternalHom.derivedSourceFunctor T)
      (DifferentialGradedModule.quasiIso B)
      ((DifferentialGradedModule.toK B).obj I) := sorry

/-- The fixed-source derived internal-Hom unit at a strict target. -/
@[stacks 070Y "strict target component of the derived internal-Hom unit"]
noncomputable abbrev unitApp (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (M : DifferentialGradedModule.{u, v} B) :=
  (InternalHom.derivedUnit T).app ((DifferentialGradedModule.toK B).obj M)

/-- The derived internal-Hom unit is invertible at a K-injective target. -/
@[stacks 070Y "K-injective derived internal-Hom unit isomorphism"]
theorem KInjective.unitApp_isIso (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :
    IsIso (unitApp T I) := sorry

/-- The canonical strict-model isomorphism at a K-injective target. -/
@[stacks 070Y "K-injective strict model of derived internal Hom"]
noncomputable def KInjective.unitIso
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :=
  @asIso _ _ _ _ (unitApp T I) (KInjective.unitApp_isIso T I hI)

/-- The derived internal-Hom unit is invertible at a property-(I) target. -/
@[stacks 070Y "property-I derived internal-Hom unit isomorphism"]
theorem PropertyI.unitApp_isIso (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.HasPropertyI B I) :
    IsIso (unitApp T I) := sorry

/-- The canonical strict-model isomorphism at a property-(I) target. -/
@[stacks 070Y "property-I strict model of derived internal Hom"]
noncomputable def PropertyI.unitIso
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    (I : DifferentialGradedModule.{u, v} B)
    (hI : DifferentialGradedModule.HasPropertyI B I) :=
  KInjective.unitIso T I
    (DifferentialGradedModule.HasPropertyI.kInjective hI)

/-- A quasi-isomorphism to a K-injective target gives a strict model of fixed-source derived
internal Hom. -/
@[stacks 070Y "K-injective replacement model of derived internal Hom"]
noncomputable def KInjective.replacementIso
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M I : DifferentialGradedModule.{u, v} B} (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :
    (DifferentialGradedModule.Derived.Q A).obj
        ((DifferentialGradedModule.toK A).obj
          (DifferentialGradedBimodule.internalHom T I)) ≅
      (InternalHom.derivedFunctor T).obj
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M)) :=
  Functor.RightDerived.ComputesAt.replacementIso
    (InternalHom.derivedSourceFunctor T) (DifferentialGradedModule.quasiIso B)
    (DifferentialGradedModule.Derived.Q B)
    ((DifferentialGradedModule.toK B).map i) hi
    (KInjective.computesAt T I hI)

/-- The forward K-injective replacement comparison is the derived unit followed by transport
along the localized replacement. -/
@[simp, stacks 070Y "forward K-injective replacement comparison for derived internal Hom"]
theorem KInjective.replacementIso_hom
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M I : DifferentialGradedModule.{u, v} B} (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :
    (KInjective.replacementIso T i hi hI).hom =
      unitApp T I ≫
        (InternalHom.derivedFunctor T).map
          (Localization.isoOfHom (DifferentialGradedModule.Derived.Q B)
            (DifferentialGradedModule.quasiIso B)
            ((DifferentialGradedModule.toK B).map i) hi).inv := sorry

/-- The inverse K-injective replacement comparison transports along the localized replacement
and then removes the derived unit at the K-injective target. -/
@[simp, stacks 070Y "inverse K-injective replacement comparison for derived internal Hom"]
theorem KInjective.replacementIso_inv
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M I : DifferentialGradedModule.{u, v} B} (i : M ⟶ I)
    (hi : DifferentialGradedModule.quasiIso B
      ((DifferentialGradedModule.toK B).map i))
    (hI : DifferentialGradedModule.Homotopy.kInjective B
      ((DifferentialGradedModule.toK B).obj I)) :
    (KInjective.replacementIso T i hi hI).inv =
      (InternalHom.derivedFunctor T).map
          (Localization.isoOfHom (DifferentialGradedModule.Derived.Q B)
            (DifferentialGradedModule.quasiIso B)
            ((DifferentialGradedModule.toK B).map i) hi).hom ≫
        (KInjective.unitIso T I hI).inv := sorry

/-- The homotopy-category replacement map underlying a property-(I) resolution. -/
@[stacks 09KU "property-I replacement map for derived internal Hom"]
def Resolution.replacement {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (DifferentialGradedModule.toK B).obj M ⟶
      (DifferentialGradedModule.toK B).obj I.obj :=
  (DifferentialGradedModule.toK B).map I.ι

/-- The replacement map of a property-(I) resolution is a quasi-isomorphism. -/
@[stacks 09KU "property-I replacement is a derived internal-Hom denominator"]
theorem Resolution.replacement_mem {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    DifferentialGradedModule.quasiIso B (Resolution.replacement I) := sorry

/-- A property-(I) resolution gives the canonical strict model of fixed-source derived
internal Hom. -/
@[stacks 0CS5 "property-I resolution model of derived internal Hom"]
noncomputable def Resolution.modelIso
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (DifferentialGradedModule.Derived.Q A).obj
        ((DifferentialGradedModule.toK A).obj
          (DifferentialGradedBimodule.internalHom T I.obj)) ≅
      (InternalHom.derivedFunctor T).obj
        ((DifferentialGradedModule.Derived.Q B).obj
          ((DifferentialGradedModule.toK B).obj M)) :=
  KInjective.replacementIso T I.ι I.quasiIso_ι
    (DifferentialGradedModule.HasPropertyI.kInjective
      (DifferentialGradedModule.PropertyI.Resolution.propertyI_obj B I))

/-- The forward resolution-model comparison is the derived unit followed by transport along
the localized replacement. -/
@[simp, stacks 0CS5 "forward property-I resolution model comparison"]
theorem Resolution.modelIso_hom
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (Resolution.modelIso T I).hom =
      unitApp T I.obj ≫
        (InternalHom.derivedFunctor T).map
          (Localization.isoOfHom (DifferentialGradedModule.Derived.Q B)
            (DifferentialGradedModule.quasiIso B) (Resolution.replacement I)
            (Resolution.replacement_mem I)).inv := sorry

/-- The inverse resolution-model comparison transports along the localized replacement and
then applies the inverse unit at the property-(I) target. -/
@[simp, stacks 0CS5 "inverse property-I resolution model comparison"]
theorem Resolution.modelIso_inv
    (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    (Resolution.modelIso T I).inv =
      (InternalHom.derivedFunctor T).map
          (Localization.isoOfHom (DifferentialGradedModule.Derived.Q B)
            (DifferentialGradedModule.quasiIso B) (Resolution.replacement I)
            (Resolution.replacement_mem I)).hom ≫
        (PropertyI.unitIso T I.obj
          (DifferentialGradedModule.PropertyI.Resolution.propertyI_obj B I)).inv := sorry

namespace Resolution

/-- The canonical comparison between the strict internal-Hom models attached to two
property-(I) resolutions of the same target. -/
@[stacks 0CS5 "change of property-I resolution for derived internal Hom"]
noncomputable def comparisonIso (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) :
    (DifferentialGradedModule.Derived.Q A).obj
        ((DifferentialGradedModule.toK A).obj
          (DifferentialGradedBimodule.internalHom T I.obj)) ≅
      (DifferentialGradedModule.Derived.Q A).obj
        ((DifferentialGradedModule.toK A).obj
          (DifferentialGradedBimodule.internalHom T J.obj)) :=
  modelIso T I ≪≫ (modelIso T J).symm

/-- The forward change-of-resolution map factors through the common abstract derived value. -/
@[simp, stacks 0CS5 "forward change-of-resolution comparison for derived internal Hom"]
theorem comparisonIso_hom (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) :
    (comparisonIso T I J).hom =
      (modelIso T I).hom ≫ (modelIso T J).inv := sorry

/-- The inverse change-of-resolution map factors through the common abstract derived value. -/
@[simp, stacks 0CS5 "inverse change-of-resolution comparison for derived internal Hom"]
theorem comparisonIso_inv (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) :
    (comparisonIso T I J).inv =
      (modelIso T J).hom ≫ (modelIso T I).inv := sorry

/-- Changing from a resolution to itself is the identity comparison. -/
@[simp, stacks 0CS5 "identity change-of-resolution comparison"]
theorem comparisonIso_refl (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I : DifferentialGradedModule.PropertyI.Resolution B M) :
    comparisonIso T I I = Iso.refl _ := sorry

/-- Reversing a change of resolution gives the inverse comparison. -/
@[simp, stacks 0CS5 "inverse change-of-resolution comparison"]
theorem comparisonIso_symm (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) :
    (comparisonIso T I J).symm = comparisonIso T J I := sorry

/-- Canonical change-of-resolution comparisons compose transitively. -/
@[simp, stacks 0CS5 "transitivity of change-of-resolution comparisons"]
theorem comparisonIso_trans (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J K : DifferentialGradedModule.PropertyI.Resolution B M) :
    comparisonIso T I J ≪≫ comparisonIso T J K = comparisonIso T I K := sorry

/-- The change-of-resolution comparison is characterized by compatibility with the common
abstract derived model. -/
@[reassoc (attr := simp), stacks 0CS5 "change-of-resolution comparison through the derived model"]
theorem comparisonIso_hom_model (T : DifferentialGradedBimodule.{u, v, w, v} A B)
    {M : DifferentialGradedModule.{u, v} B}
    (I J : DifferentialGradedModule.PropertyI.Resolution B M) :
    (comparisonIso T I J).hom ≫ (modelIso T J).hom =
      (modelIso T I).hom := sorry

end Resolution

end DifferentialGradedBimodule.InternalHom.Derived
