/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.Simplicial.WeaklyContractible

/-!
# Weakly contractible hypercover descent on the small pro-étale site
-/

@[expose] public section

open CategoryTheory Opposite
open DerivedCategory.Plus (Q)

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Derived sections over any object of the small pro-étale site are computed by the total
Čech complex of a bounded-below coefficient complex on a degreewise weakly contractible
singleton hypercover. -/
theorem rGamma_isIsomorphic_totalCech {X : Scheme.{u}}
    [HasSheafify (topology X) AddCommGrpCat.{u}]
    [IsGrothendieckAbelian (Sheaf (topology X) AddCommGrpCat.{u})] (U : X.ProEt)
    [Functor.HasRightDerivedFunctor
      ((siteAbelianSectionsFunctor (topology X) U).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh)
      (HomotopyCategory.Plus.quasiIso (Sheaf (topology X) AddCommGrpCat.{u}))]
    (K : SimplicialObject (Over U))
    (hK : SimplicialObject.IsSingletonHypercover (topology X) K)
    (hW : ∀ n : ℕ,
      (topology X).IsWeaklyContractible ((K.obj (op (SimplexCategory.mk n))).left))
    (ℰ : CochainComplex.Plus (Sheaf (topology X) AddCommGrpCat.{u})) :
    IsIsomorphic
      ((siteAbelianSectionsBoundedBelowDerived (topology X) U ⋙
        DerivedCategory.Plus.ι).obj (Q.obj ℰ))
      (DerivedCategory.Q.obj ((SimplicialObject.Cech.totalFunctor K).obj ℰ.obj)) := sorry

end AlgebraicGeometry.Scheme.ProEt
