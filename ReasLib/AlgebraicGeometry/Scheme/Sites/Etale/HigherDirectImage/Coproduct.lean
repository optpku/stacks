/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.HigherDirectImage.Complex
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Coproducts
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Limits.Shapes.Products

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{u + 1, u + 1, u + 1}
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})]
variable [((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
    Y.smallEtaleTopology X.smallEtaleTopology).Additive]
variable [Functor.HasRightDerivedFunctor
    (RightDerived.Cochain.toDerived
      ((smallEtalePullback f).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology X.smallEtaleTopology))
    (HomologicalComplex.quasiIso
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (ComplexShape.up ℤ))]
variable {I : Type u}
variable (K : I → DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}))]
variable [HasCoproductsOfShape I (DerivedCategory (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}))]

/-- The canonical comparison from the coproduct of derived pushforwards to the derived
pushforward of the coproduct is an isomorphism for a quasi-compact, quasi-separated morphism
on a uniformly bounded-below family of abelian étale sheaves. -/
theorem etaleDerivedPushforward_preservesCoproduct [QuasiCompact f] [QuasiSeparated f]
    (a : ℤ) (hK : ∀ i : I, DerivedCategory.IsGE (K i) a) :
    IsIso (CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K) := sorry

/-- The homology map induced by the derived-pushforward coproduct comparison is an isomorphism
in every degree under the same bounded-below and geometric hypotheses. -/
theorem etaleDerivedPushforward_preservesCoproduct_homology
    [QuasiCompact f] [QuasiSeparated f] (a : ℤ) (hK : ∀ i : I, DerivedCategory.IsGE (K i) a) (p : ℤ) :
    IsIso
      ((DerivedCategory.homologyFunctor (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) p).map
        (CategoryTheory.Limits.sigmaComparison (etaleAbelianPushforwardDerived f) K)) := sorry

end AlgebraicGeometry.Scheme.Etale

end
