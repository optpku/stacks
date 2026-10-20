/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Data.ZMod.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The unbounded derived direct image on small étale sheaves of `ZMod n`-modules
preserves arbitrary coproducts along a proper morphism when `n` is positive. -/
@[stacks 0F0D]
theorem etalePushforwardDerived_preservesCoproducts_of_isProper
    (f : X ⟶ Y) [IsProper f] (n : ℕ) (hn : 0 < n)
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]
    (I : Type u)
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))] :
    PreservesColimitsOfShape (Discrete I)
      (RightDerived.Cochain.functor
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology)) := sorry

/-- The unbounded derived direct image along a proper morphism preserves coproducts
for sheaves of modules over `ZMod n` when `n` is nonzero. -/
instance etalePushforwardDerived_preservesCoproducts
    (f : X ⟶ Y) [IsProper f] (n : ℕ) [NeZero n]
    [HasSheafify X.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n)))]
    [((smallEtalePullback f).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology).Additive]
    [HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))) (ComplexShape.up ℤ))]
    (I : Type u)
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} (ZMod n))))]
    [HasColimitsOfShape (Discrete I)
      (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} (ZMod n))))] :
    PreservesColimitsOfShape (Discrete I)
      (RightDerived.Cochain.functor
        ((smallEtalePullback f).sheafPushforwardContinuous
          (ModuleCat.{u} (ZMod n)) Y.smallEtaleTopology X.smallEtaleTopology)) :=
  etalePushforwardDerived_preservesCoproducts_of_isProper f n (NeZero.pos n) I

end AlgebraicGeometry.Scheme

end
