/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Restriction
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.RingTheory.Henselian

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- For a henselian pair, restriction of a locally torsion abelian étale sheaf
to the quotient spectrum induces an isomorphism on cohomology in every degree. -/
theorem etaleCohomologyRestrict_isIso_of_henselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    [HasSheafify (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of A)).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of A)).smallEtaleTopology
        (terminal (Spec (CommRingCat.of A)).Etale)).Additive]
    [HasSheafify (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of (A ⧸ I))).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology
        (terminal (Spec (CommRingCat.of (A ⧸ I))).Etale)).Additive]
    [((smallEtalePullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (Spec (CommRingCat.of A)).smallEtaleTopology
        (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})
    (hF : Sheaf.IsLocallyTorsion F) (q : ℕ) :
    IsIso (etaleCohomologyRestrict
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) :=
  sorry

/-- Cohomology restriction to the quotient of a henselian pair is invertible
for locally torsion abelian étale coefficients. -/
@[instance] theorem instIsIsoEtaleCohomologyRestrictOfHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    [HasSheafify (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of A)).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of A)).smallEtaleTopology
        (terminal (Spec (CommRingCat.of A)).Etale)).Additive]
    [HasSheafify (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions
      (Sheaf (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal (Spec (CommRingCat.of (A ⧸ I))).Etale]
    [(siteAbelianSectionsFunctor (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology
        (terminal (Spec (CommRingCat.of (A ⧸ I))).Etale)).Additive]
    [((smallEtalePullback
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).sheafPushforwardContinuous
        AddCommGrpCat.{u}
        (Spec (CommRingCat.of A)).smallEtaleTopology
        (Spec (CommRingCat.of (A ⧸ I))).smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf (Spec (CommRingCat.of A)).smallEtaleTopology AddCommGrpCat.{u})
    [Fact (Sheaf.IsLocallyTorsion F)] (q : ℕ) :
    IsIso (etaleCohomologyRestrict
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) F q) :=
  etaleCohomologyRestrict_isIso_of_henselianPair I F
    (Fact.elim (inferInstance : Fact (Sheaf.IsLocallyTorsion F))) q

end AlgebraicGeometry.Scheme.Etale
