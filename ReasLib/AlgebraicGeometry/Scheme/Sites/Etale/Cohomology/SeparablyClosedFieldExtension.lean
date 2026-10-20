/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.BoundedBelow.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.BoundedBelow.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe w u

namespace AlgebraicGeometry.Scheme.Etale

variable [∀ Z : Scheme.{u}, HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ {A B : Scheme.{u}} (h : A ⟶ B),
    ((smallEtalePullback h).sheafPushforwardContinuous AddCommGrpCat.{u}
      B.smallEtaleTopology A.smallEtaleTopology).IsRightAdjoint]
variable [∀ Z : Scheme.{u},
    HasDerivedCategory.{w} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    ((siteAbelianSectionsFunctor Z.smallEtaleTopology (globalEtale Z)).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}))]

/-- Extension of separably closed fields preserves every integer-degree étale hypercohomology
group of a quasi-compact quasi-separated scheme for bounded-below complexes whose cohomology
sheaves have torsion geometric stalks of orders invertible in the base field. -/
theorem derivedEtaleCohomologyRestrict_isIso_of_sepClosedFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f) ⋙
        siteAbelianSectionsFunctor
          (FieldExtension.baseChange k K f).smallEtaleTopology
          (globalEtale (FieldExtension.baseChange k K f))).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)
    (q : ℤ) :
    IsIso (derivedEtaleCohomologyRestrict (FieldExtension.toSource k K f) E q) := sorry

/-- For a quasi-compact quasi-separated scheme over a separably closed field, the derived
adjunction unit for extension to a separably closed field is an isomorphism on bounded-below
complexes whose cohomology sheaves have torsion geometric stalks of invertible orders. -/
theorem etaleDerivedAdjunctionUnit_isIso_of_sepClosedFieldExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(abelianPushforwardAlong (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E) :
    IsIso (etaleDerivedAdjunctionUnit (FieldExtension.toSource k K f) E) := sorry

/-- The étale hypercohomology restriction for a separably closed field extension is an
isomorphism when the invertible-order torsion cohomology condition is supplied by `Fact`. -/
instance derivedEtaleCohomologyRestrict_isIso_of_sepClosedFieldExtension_of_fact
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    [(etaleAbelianSheafPullback (FieldExtension.toSource k K f) ⋙
        siteAbelianSectionsFunctor
          (FieldExtension.baseChange k K f).smallEtaleTopology
          (globalEtale (FieldExtension.baseChange k K f))).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    [Fact (DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)]
    (q : ℤ) :
    IsIso (derivedEtaleCohomologyRestrict (FieldExtension.toSource k K f) E q) :=
  derivedEtaleCohomologyRestrict_isIso_of_sepClosedFieldExtension f E Fact.out q

/-- The derived adjunction unit for a separably closed field extension is an isomorphism
when the invertible-order torsion cohomology condition is supplied by `Fact`. -/
instance etaleDerivedAdjunctionUnit_isIso_of_sepClosedFieldExtension_of_fact
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [QuasiSeparated f]
    [(abelianPushforwardAlong (FieldExtension.toSource k K f)).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u}))]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
    [Fact (DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn (Spec (CommRingCat.of k)) :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})) E)] :
    IsIso (etaleDerivedAdjunctionUnit (FieldExtension.toSource k K f) E) :=
  etaleDerivedAdjunctionUnit_isIso_of_sepClosedFieldExtension f E Fact.out

end AlgebraicGeometry.Scheme.Etale

end

end
