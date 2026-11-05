module

public import Mathlib.Algebra.Homology.QuasiIso
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Basic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.StrictlyPerfect

@[expose] public section

/-!
# Perfect complexes on ringed sites

This file owns perfectness before passage to a derived category.  A perfect complex is locally
quasi-isomorphic to a strictly perfect complex; both the object property and its full subcategory
are available without importing derived-category infrastructure.
-/

open CategoryTheory
open CategoryTheory.Limits
open RingedSite.Hom

noncomputable section

universe u v w

namespace RingedSite.CochainComplex

section Model

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [X.siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Complexes admitting a strictly perfect quasi-isomorphic model, as an object property. -/
def hasStrictlyPerfectModel :
    ObjectProperty (CochainComplex (ModuleCat.{w} X) ℤ) :=
  fun E ↦ ∃ E' : CochainComplex (ModuleCat.{w} X) ℤ,
    ∃ α : E' ⟶ E, IsStrictlyPerfect E' ∧ QuasiIso α

/-- A complex of modules on a ringed site has a strictly perfect model if it receives a
quasi-isomorphism from a strictly perfect complex. -/
abbrev HasStrictlyPerfectModel
    (E : CochainComplex (ModuleCat.{w} X) ℤ) : Prop :=
  hasStrictlyPerfectModel (X := X) E

/-- Having a strictly perfect model unfolds to a strictly perfect source and a
quasi-isomorphism to the given complex. -/
theorem hasStrictlyPerfectModel_iff
    (E : CochainComplex (ModuleCat.{w} X) ℤ) :
    HasStrictlyPerfectModel E ↔
      ∃ E' : CochainComplex (ModuleCat.{w} X) ℤ,
        ∃ α : E' ⟶ E, IsStrictlyPerfect E' ∧ QuasiIso α := sorry

/-- Admitting a strictly perfect model is invariant under isomorphisms of complexes. -/
instance hasStrictlyPerfectModel_isClosedUnderIsomorphisms :
    (hasStrictlyPerfectModel (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport a strictly perfect model along an isomorphism of complexes. -/
theorem HasStrictlyPerfectModel.of_iso
    {E F : CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : HasStrictlyPerfectModel E) (e : E ≅ F) :
    HasStrictlyPerfectModel F := sorry

end Model

section Local

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X.carrier,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X.carrier,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Perfect complexes of modules on a ringed site, as an object property. -/
def perfect : ObjectProperty (CochainComplex (ModuleCat.{w} X) ℤ) :=
  fun E ↦ ∀ U : X.carrier, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
    HasStrictlyPerfectModel ((localizedRestrictionComplex.{w} X I.Y).obj E)

/-- A complex of modules on a ringed site is perfect when every localized restriction has a
cover by strictly perfect quasi-isomorphic models. -/
@[stacks 08G5]
abbrev IsPerfect (E : CochainComplex (ModuleCat.{w} X) ℤ) : Prop :=
  perfect (X := X) E

/-- Perfect complexes on a ringed site, as a full subcategory. -/
@[stacks 08G5 "(1), full subcategory"]
abbrev Perfect :=
  (perfect (X := X)).FullSubcategory

namespace Perfect

/-- The canonical inclusion of perfect complexes on a ringed site. -/
abbrev ι : Perfect (X := X) ⥤ CochainComplex (ModuleCat.{w} X) ℤ :=
  ObjectProperty.ι _

end Perfect

/-- Perfectness of a complex unfolds to strict-perfect quasi-isomorphic local models on a cover
of every localization. -/
theorem isPerfect_iff (E : CochainComplex (ModuleCat.{w} X) ℤ) :
    IsPerfect E ↔
      ∀ U : X.carrier, ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
        HasStrictlyPerfectModel ((localizedRestrictionComplex.{w} X I.Y).obj E) := sorry

/-- A perfect complex supplies a cover by strictly perfect models over every object of the
site. -/
theorem IsPerfect.exists_cover
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsPerfect E) (U : X.carrier) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      HasStrictlyPerfectModel ((localizedRestrictionComplex.{w} X I.Y).obj E) := sorry

/-- A perfect complex admits a strictly perfect local model over every localization. -/
theorem exists_strictlyPerfect_localModel
    {E : CochainComplex (ModuleCat.{w} X) ℤ} (hE : IsPerfect E) (U : X.carrier) :
    ∃ T : X.siteTopology.Cover U, ∀ I : T.Arrow,
      ∃ E' : CochainComplex (ModuleCat.{w} (X.localization I.Y)) ℤ,
        ∃ α : E' ⟶ (localizedRestrictionComplex.{w} X I.Y).obj E,
          IsStrictlyPerfect E' ∧ QuasiIso α := sorry

/-- Perfect complexes on a ringed site are stable under isomorphism. -/
instance perfect_isClosedUnderIsomorphisms :
    (perfect (X := X)).IsClosedUnderIsomorphisms := sorry

/-- Transport perfectness along an isomorphism of complexes. -/
theorem IsPerfect.of_iso
    {E F : CochainComplex (ModuleCat.{w} X) ℤ}
    (hE : IsPerfect E) (e : E ≅ F) :
    IsPerfect F := sorry

end Local

end RingedSite.CochainComplex


-- These definitions expose their local models explicitly; their computational/witness content
-- must not depend on `sorryAx`.
