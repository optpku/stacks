/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantPullback
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.FieldTheory.IsSepClosed

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme CategoryTheory.Sheaf

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a proper scheme over a separably closed field, extension to a separably closed
field induces an isomorphism on étale cohomology with locally torsion abelian coefficients
in every nonnegative degree. -/
theorem etaleCohomologyRestrict_isIso_of_isProper_sepClosed
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [Abelian (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (FieldExtension.baseChange k K f).Etale]
    [(siteAbelianSectionsFunctor (FieldExtension.baseChange k K f).smallEtaleTopology
      (terminal (FieldExtension.baseChange k K f).Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.toSource k K f) F q) := sorry

/-- Local torsion supplied as a fact makes cohomology restriction along an extension of
separably closed fields an isomorphism for a proper scheme in every nonnegative degree. -/
instance etaleCohomologyRestrict_isIso_of_isProper_sepClosed_of_fact
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsSepClosed k] [IsSepClosed K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [Abelian (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (FieldExtension.baseChange k K f).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (FieldExtension.baseChange k K f).Etale]
    [(siteAbelianSectionsFunctor (FieldExtension.baseChange k K f).smallEtaleTopology
      (terminal (FieldExtension.baseChange k K f).Etale)).Additive]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [Fact (IsLocallyTorsion F)] (q : ℕ) :
    IsIso (etaleCohomologyRestrict (FieldExtension.toSource k K f) F q) :=
  etaleCohomologyRestrict_isIso_of_isProper_sepClosed k K f F Fact.out q

end AlgebraicGeometry.Scheme.Etale

end
