/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Module.ZMod
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.CategoryTheory.Monoidal.Flat
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import stacks_project.Chap59.Definition_59_70_1_ExtensionByZero
public import stacks_project.Chap59.Lemma_59_92_3_BaseChange
public import ReasLib.CategoryTheory.Sites.Pullback.SheafCompose
public import stacks_project.Chap59.Theorem_59_51_3_Cohomology
public import stacks_project.Chap64.«64_2_0_1_GeometricFrobenius»

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.CompactSupport.FiniteCoefficients

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory

universe u

#check (AlgebraicGeometry.Scheme.Etale.etaleCohomologyCompactSupport :
  ∀ {k : Type u} [Field k] {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [HasWeakSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt
      (Sheaf
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
        AddCommGrpCat.{u})]
    [(FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})],
    ModuleCat.{u} (ZMod (ℓ ^ n)))
