/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect

@[expose] public section

/-!
# Locally strictly perfect complexes on ringed sites

This leaf owns local strict perfectness for complexes of module sheaves on a bundled ringed
site.
-/

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (localizedRestrictionComplex)

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

section

variable {X : RingedSite.{u, v, w}}
variable [UnivLE.{max u v, w}]
variable [∀ U : X, HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Complexes that are strictly perfect locally on the site, as an object property. -/
@[stacks 0FPR "object property"]
def locallyStrictlyPerfect :
    ObjectProperty (CochainComplex (ModuleCat.{w} X) ℤ) :=
  fun E ↦ ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    IsStrictlyPerfect ((localizedRestrictionComplex.{w} X I.Y).obj E)

/-- A complex of modules on a ringed site is locally strictly perfect when it belongs to
`locallyStrictlyPerfect`. This is an ordinary mathematical predicate, not ambient instance data. -/
@[stacks 0FPR "predicate"]
abbrev IsLocallyStrictlyPerfect
    (E : CochainComplex (ModuleCat.{w} X) ℤ) : Prop :=
  locallyStrictlyPerfect E

/-- Locally strictly perfect complexes on a ringed site, as a full subcategory. -/
abbrev LocallyStrictlyPerfect :=
  (locallyStrictlyPerfect (X := X)).FullSubcategory

namespace LocallyStrictlyPerfect

/-- The canonical inclusion of locally strictly perfect complexes. -/
abbrev ι : LocallyStrictlyPerfect (X := X) ⥤ CochainComplex (ModuleCat.{w} X) ℤ :=
  ObjectProperty.ι _

end LocallyStrictlyPerfect

/-- Local strict perfectness unfolds to the covering criterion by strictly perfect localized
restrictions. -/
theorem isLocallyStrictlyPerfect_iff (E : CochainComplex (ModuleCat.{w} X) ℤ) :
    IsLocallyStrictlyPerfect E ↔
      ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        IsStrictlyPerfect ((localizedRestrictionComplex.{w} X I.Y).obj E) := sorry

/-- Cover-wise strict perfectness constructs a locally strictly perfect complex. -/
theorem isLocallyStrictlyPerfect_of_cover
    {E : CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : ∀ U : X, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      IsStrictlyPerfect ((localizedRestrictionComplex.{w} X I.Y).obj E)) :
    IsLocallyStrictlyPerfect E := sorry

/-- A locally strictly perfect complex supplies a strict-perfect cover over every site object. -/
theorem IsLocallyStrictlyPerfect.exists_cover
    {E : CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : IsLocallyStrictlyPerfect E) (U : X) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      IsStrictlyPerfect ((localizedRestrictionComplex.{w} X I.Y).obj E) := sorry

/-- Local strict perfectness is invariant under isomorphisms of complexes. -/
instance locallyStrictlyPerfect_isClosedUnderIsomorphisms :
    (locallyStrictlyPerfect (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport local strict perfectness along an isomorphism of complexes. -/
theorem IsLocallyStrictlyPerfect.of_iso
    {E F : CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : IsLocallyStrictlyPerfect E) (e : E ≅ F) :
    IsLocallyStrictlyPerfect F := sorry

end

end RingedSite.CochainComplex
