/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.Topology.Specialization.Dimension

/-!
# Algebraic field-extension pullback of Chow groups

This file specializes flat base change of Chow groups along `Spec K ⟶ Spec k` for a field
extension `K / k`, and records that the kernel is torsion when the extension is algebraic.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.FieldExtension

/-- The structure morphism `Spec K ⟶ Spec k` of a field extension is compatible with the
constant-zero dimension functions, with relative-dimension shift zero. -/
theorem algebraicExtensionStructureMap_compatible
    (k K : Type u) [Field k] [Field K] [Algebra k K] :
    @Scheme.Hom.IsDimensionFunctionCompatible
      (Spec (CommRingCat.of k)) (Spec (CommRingCat.of K))
      (@AlgebraicGeometry.instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
      (@AlgebraicGeometry.instUniversallyCatenarySpec K _
        (@instUniversallyCatenaryRingOfField.{u, u} K _))
      (specMap k K) inferInstance
      (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
      (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)
      (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
      (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance) 0 := sorry

/-- Flat pullback on degree-`i` Chow groups along the field extension `K / k`. -/
noncomputable def algebraicExtensionPullback
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ) :
    @ChowGroup X.left
        (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
          inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _)).toIsLocallyNoetherian)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction X.left
          (Spec (CommRingCat.of k)) X.hom
          (@AlgebraicGeometry.instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _))
          inferInstance (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)) i →+
      @ChowGroup (pullback X.hom (specMap k K))
        (@LocallyOfFiniteType.isLocallyNoetherian (pullback X.hom (specMap k K))
          (Spec (CommRingCat.of K)) (pullback.snd X.hom (specMap k K)) inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
        ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
          (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
          (pullback.snd X.hom (specMap k K))
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _))
          inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance)) i :=
  (@reindex (pullback X.hom (specMap k K))
      (@LocallyOfFiniteType.isLocallyNoetherian (pullback X.hom (specMap k K))
        (Spec (CommRingCat.of K)) (pullback.snd X.hom (specMap k K)) inferInstance
        (@AlgebraicGeometry.instUniversallyCatenarySpec K _
          (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
      ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
        (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
        (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
        (pullback.snd X.hom (specMap k K))
        (@AlgebraicGeometry.instUniversallyCatenarySpec K _
          (@instUniversallyCatenaryRingOfField.{u, u} K _))
        inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
        (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance))
      (i + 0) i (add_zero i)).toAddMonoidHom.comp
    (@baseChangePullback (Spec (CommRingCat.of k)) (Spec (CommRingCat.of K)) X.left
      (@AlgebraicGeometry.instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
      (@AlgebraicGeometry.instUniversallyCatenarySpec K _
        (@instUniversallyCatenaryRingOfField.{u, u} K _))
      (specMap k K) inferInstance
      (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
      (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)
      (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
      (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance) 0
      (algebraicExtensionStructureMap_compatible k K) X.hom inferInstance i)

/-- The algebraic-extension pullback sends a Chow class to the reindexed class of
the cycle-theoretic base-change pullback. -/
theorem algebraicExtensionPullback_chowClass
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ)
    (α : CycleGroup X.left
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) i) :
    algebraicExtensionPullback k K X i
        (@chowClass X.left
          (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
            inferInstance
            (@AlgebraicGeometry.instUniversallyCatenarySpec k _
              (@instUniversallyCatenaryRingOfField.{u, u} k _)).toIsLocallyNoetherian)
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction X.left
            (Spec (CommRingCat.of k)) X.hom
            (@AlgebraicGeometry.instUniversallyCatenarySpec k _
              (@instUniversallyCatenaryRingOfField.{u, u} k _))
            inferInstance (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
            (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)) i α) =
      @reindex (pullback X.hom (specMap k K))
        (@LocallyOfFiniteType.isLocallyNoetherian (pullback X.hom (specMap k K))
          (Spec (CommRingCat.of K)) (pullback.snd X.hom (specMap k K)) inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
        ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
          (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
          (pullback.snd X.hom (specMap k K))
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _))
          inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance))
        (i + 0) i (add_zero i)
        (@chowClass (pullback X.hom (specMap k K))
          (@LocallyOfFiniteType.isLocallyNoetherian (pullback X.hom (specMap k K))
            (Spec (CommRingCat.of K)) (pullback.snd X.hom (specMap k K)) inferInstance
            (@AlgebraicGeometry.instUniversallyCatenarySpec K _
              (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
          ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
            (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
          (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
            (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
            (pullback.snd X.hom (specMap k K))
            (@AlgebraicGeometry.instUniversallyCatenarySpec K _
              (@instUniversallyCatenaryRingOfField.{u, u} K _))
            inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
            (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance)) (i + 0)
          (CycleGroup.baseChangePullback (specMap k K)
            (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
            (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)) 0
            (algebraicExtensionStructureMap_compatible k K) X.hom i α)) := sorry

/-- For an algebraic field extension `K / k` and a finite-type `k`-scheme `X`, the kernel of
flat pullback `CH_i(X) → CH_i(X_K)` is a torsion abelian group. -/
theorem algebraicExtensionPullback_ker_isTorsion
    (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
    (X : Over (Spec (CommRingCat.of k))) [Scheme.Hom.FiniteType X.hom] (i : ℤ) :
    AddMonoid.IsTorsion (algebraicExtensionPullback k K X i).ker := sorry

end AlgebraicGeometry.ChowGroup.FieldExtension
