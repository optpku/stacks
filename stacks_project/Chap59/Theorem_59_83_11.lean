/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Curve.Vanishing
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

universe u

/- Theorem 59.83.11. Locally torsion abelian étale sheaves on finite-type schemes of
dimension at most one over an algebraically closed field have zero cohomology in degrees
at least three, and affine schemes also have zero degree-two cohomology. -/
@[stacks 03RT] #check
  (AlgebraicGeometry.Etale.TorsionOnCurve.etaleCohomology_isZero_of_ge_three :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasTerminal X.left.Etale]
      [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
      (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
      {q : ℕ} (hq : 2 < q), IsZero (etaleCohomology X.left F q))

#check
  (AlgebraicGeometry.Etale.TorsionOnCurve.etaleCohomology_h2_isZero_of_isAffine :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasTerminal X.left.Etale]
      [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
      (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
      (h_affine : IsAffine X.left), IsZero (etaleCohomology X.left F 2))

#check
  (AlgebraicGeometry.Etale.TorsionOnCurve.etaleCohomology_isZero_of_isAffine_gt_one :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom]
      (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
      [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
      [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
      [HasTerminal X.left.Etale]
      [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]
      (hF : IsLocallyTorsion F) (h_dim : topologicalKrullDim X.left ≤ 1)
      (h_affine : IsAffine X.left) {q : ℕ} (hq : 1 < q),
      IsZero (etaleCohomology X.left F q))
