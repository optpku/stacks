/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProEtaleDerived

/-!
# Derived étale-to-pro-étale adjunction

The bounded-below derived adjunction `ε⁻¹ ⊣ Rε_*` induced by `etaleToProEt`.
-/

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

variable (X : Scheme.{u})
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1},
    (etaleToProEt X).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
variable [HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1}]

#check
  (AlgebraicGeometry.Scheme.etaleToProEtSheaf_hasRightDerivedFunctor X :
    (etaleToProEtSheaf X AddCommGrpCat.{u + 1}).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso
        (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusPushforward X :
    DerivedCategory.Plus (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusPushforward_eq X :
    etaleToProEt_plusPushforward X =
      Adjunction.Derived.Plus.right (etaleToProEtSheaf X AddCommGrpCat.{u + 1}))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_sheafAdjunction_addCommGrp_unit_app_isIso X :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      IsIso ((etaleToProEt_sheafAdjunction X AddCommGrpCat.{u + 1}).unit.app F))

#check
  (AlgebraicGeometry.Scheme.etaleToProEtSheaf_rightDerived_pullback_isZero X :
    ∀ (I : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) [Injective I]
      (q : ℕ), 0 < q →
      IsZero
        (((etaleToProEtSheaf X AddCommGrpCat.{u + 1}).rightDerived q).obj
          ((etaleToProEtPullback X AddCommGrpCat.{u + 1}).obj I)))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusPullback X :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory.Plus (Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusPullback_eq X :
    etaleToProEt_plusPullback X =
      Adjunction.Derived.Plus.left
        (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1})))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusAdjunction X :
    etaleToProEt_plusPullback X ⊣ etaleToProEt_plusPushforward X)

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_plusAdjunction_eq X :
    etaleToProEt_plusAdjunction X =
      Adjunction.Derived.Plus.adjunction
        (ExactFunctor.of (etaleToProEtPullback X AddCommGrpCat.{u + 1}))
        (etaleToProEtSheaf X AddCommGrpCat.{u + 1})
        (etaleToProEt_sheafAdjunction X AddCommGrpCat.{u + 1}))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_derivedUnit X :
    ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      K ⟶ (etaleToProEt_plusPushforward X).obj ((etaleToProEt_plusPullback X).obj K))

#check
  (AlgebraicGeometry.Scheme.etaleToProEt_derivedUnit_eq X :
    ∀ K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      etaleToProEt_derivedUnit X K = (etaleToProEt_plusAdjunction X).unit.app K)

end
