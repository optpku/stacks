/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Leray
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.AbelianPullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ConcreteCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- A positive-degree étale cohomology class of a torsion abelian sheaf restricted
to a closed subscheme of an affine scheme vanishes after a monomorphic extension
to another torsion abelian sheaf on the ambient scheme. -/
theorem exists_injective_locallyTorsion_etaleCohomology_eq_zero
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X.Etale]
    [(siteAbelianSectionsFunctor X.smallEtaleTopology (terminal X.Etale)).Additive]
    [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
    [Abelian (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal Z.Etale]
    [(siteAbelianSectionsFunctor Z.smallEtaleTopology (terminal Z.Etale)).Additive]
    [((smallEtalePullback i).sheafPushforwardContinuous AddCommGrpCat.{u}
        X.smallEtaleTopology Z.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (hF : Sheaf.IsLocallyTorsion F) {q : ℕ} (hq : 0 < q)
    (ξ : (CategoryTheory.forget AddCommGrpCat).obj
      (etaleCohomology Z ((etaleAbelianRestriction i).obj F) q)) :
    ∃ (F' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (φ : F ⟶ F'),
      Mono φ ∧ Sheaf.IsLocallyTorsion F' ∧
        (CategoryTheory.forget AddCommGrpCat).map
            (etaleCohomology_map ((etaleAbelianRestriction i).map φ) q) ξ = 0 :=
  sorry

end AlgebraicGeometry.Scheme.Etale
