/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle.ClosedImmersion
public import stacks_project.Chap42.Lemma_42_54_2_BivariantClass

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle
open scoped DirectSum

universe u

/- Lemma 42.54.2: deformation to the normal cone defines a completed bivariant class. -/
@[stacks 0FBK] #check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass :
  ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V),
    BivariantClass.OpenRestriction.Completion delta (overHom q p i hi)
      (fun r : ℕ ↦ @rankOpen Z X i
        (inferInstance : IsImmersion i) V r)
      (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
      (fun r ↦ rankOpen_le_preimage_top q p i hi V r))

/- Cartesian base change restricts the completed class. -/
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_pullback :
  ∀ {S Z X Z' X' : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    (q' : Z' ⟶ S) (p' : X' ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    [LocallyOfFiniteType q'] [LocallyOfFiniteType p']
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (i' : Z' ⟶ X') (hi' : i' ≫ p' = q') [h_i' : IsClosedImmersion i']
    (g : Over.mk q' ⟶ Over.mk q) (f : Over.mk p' ⟶ Over.mk p)
    (square : IsPullback g.left i' i f.left)
    (V : VirtualNormalBundle i)
    (D : ClosedDeformation q p i hi V)
    (D' : ClosedDeformation q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V)),
    closedClass delta q' p' i' hi'
      (@VirtualNormalBundle.pullback Z X Z' X' g.left i' i f.left
        (IsImmersion.instOfIsClosedImmersion i') (IsImmersion.instOfIsClosedImmersion i)
        square V) D' =
      closedClassBaseChange delta q p q' p' i hi i' hi' g f square V D)

/- Constant rank gives a homogeneous class of that degree. -/
#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.closedClass_eq_completeOfRank :
  ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [h_i : IsClosedImmersion i]
    (V : VirtualNormalBundle i) (D : ClosedDeformation q p i hi V) (r : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank r V.module],
    closedClass delta q p i hi V D =
      BivariantClass.OpenRestriction.Completion.complete delta
        (overHom q p i hi)
        (fun n : ℕ ↦ @rankOpen Z X i
          (inferInstance : IsImmersion i) V n)
        (fun _ : Unit ↦ ⊤) (fun _ ↦ Unit.unit)
        (fun n ↦ rankOpen_le_preimage_top q p i hi V n)
        (@DirectSum.of ℕ
          (fun n : ℕ ↦ BivariantClass delta (overHom q p i hi) (n : ℤ))
          (fun n ↦ (BivariantClass.pointwiseAddCommGroup delta
            (overHom q p i hi) (n : ℤ)).toAddCommMonoid)
          inferInstance r (globalClassOfRank delta q p i hi V D r)))
