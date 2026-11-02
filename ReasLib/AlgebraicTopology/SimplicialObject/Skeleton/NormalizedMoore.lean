/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Generated
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 017Y

# Normalized Moore complexes of simplicial skeleta

The bounded-degree generated object and the left Kan extension of an `m`-truncated simplicial
object have no normalized Moore part above degree `m`. The source-facing theorems use the
lower-face convention; symmetric upper-face companions remain available for Mathlib consumers.
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

section

variable {A : Type u} [Category.{v} A] [Abelian A]

set_option backward.isDefEq.respectTransparency false in
private lemma normalizedMoore_eq_bot_of_projector_eq_zero (U : SimplicialObject A)
    (n : ℕ) (h : (DoldKan.PInfty (X := U)).f n = 0) :
    NormalizedMooreComplex.objX U n = ⊥ := by
  rw [← Subobject.mk_arrow (NormalizedMooreComplex.objX U n),
    Subobject.mk_eq_bot_iff_zero]
  have hi := HomologicalComplex.congr_hom
    (DoldKan.inclusionOfMooreComplexMap_comp_PInfty U) n
  change (NormalizedMooreComplex.objX U n).arrow ≫ (DoldKan.PInfty (X := U)).f n =
    (NormalizedMooreComplex.objX U n).arrow at hi
  simpa [h] using hi.symm

set_option backward.isDefEq.respectTransparency false in
private lemma normalizedMoore_eq_bot_of_mono {U V : SimplicialObject A}
    (f : V ⟶ U) (n : ℕ) [Mono (f.app (op ⦋n⦌))]
    (h : f.app (op ⦋n⦌) ≫ (DoldKan.PInfty (X := U)).f n = 0) :
    NormalizedMooreComplex.objX V n = ⊥ := by
  apply normalizedMoore_eq_bot_of_projector_eq_zero
  apply (cancel_mono (f.app (op ⦋n⦌))).1
  rw [Limits.zero_comp, ← DoldKan.PInfty_f_naturality n f, h]

private lemma map_comp_projector_eq_zero (U : SimplicialObject A) (n : ℕ)
    {Delta : SimplexCategory} (theta : ⦋n⦌ ⟶ Delta) (h : Delta.len < n) :
    U.map theta.op ≫ (DoldKan.PInfty (X := U)).f n = 0 := by
  apply DoldKan.degeneracy_comp_PInfty
  intro htheta
  letI := htheta
  exact (Nat.not_le_of_gt h) (SimplexCategory.len_le_of_mono theta)

set_option backward.isDefEq.respectTransparency false in
private lemma map_comp_lowerFace_projector_eq_zero (U : SimplicialObject A) (n : ℕ)
    {Delta : SimplexCategory} (theta : ⦋n⦌ ⟶ Delta) (h : Delta.len < n) :
    U.map theta.op ≫
      (DoldKan.PInfty (X := _root_.SimplicialObject.opFunctor.obj U)).f n = 0 := by
  have hrev := map_comp_projector_eq_zero (_root_.SimplicialObject.opFunctor.obj U) n
    (SimplexCategory.rev.map theta) h
  change U.map (SimplexCategory.rev.map (SimplexCategory.rev.map theta)).op ≫
    (DoldKan.PInfty (X := _root_.SimplicialObject.opFunctor.obj U)).f n = 0 at hrev
  simpa only [SimplexCategory.rev_map_rev_map] using hrev

set_option backward.isDefEq.respectTransparency false in
private lemma generated_arrow_comp_eq_zero (U : SimplicialObject A) (n m : ℕ)
    {T : A} (p : U.obj (op ⦋m⦌) ⟶ T)
    (hp : ∀ (i : ℕ), i ≤ n → ∀ theta : ⦋m⦌ ⟶ ⦋i⦌, U.map theta.op ≫ p = 0) :
    (U.generated n).arrow.app (op ⦋m⦌) ≫ p = 0 := by
  have hle : generated.degree U n ⦋m⦌ ≤ Limits.kernelSubobject p := by
    unfold generated.degree
    apply Finset.sup'_le
    intro i hi
    exact Limits.imageSubobject_le _
      (Limits.factorThruKernelSubobject p _
        (hp i.1.1 (Nat.le_of_lt_succ i.1.2) i.2))
      (by simp)
  have hdegree : (generated.degree U n ⦋m⦌).arrow ≫ p = 0 := by
    rw [← Subobject.ofLE_arrow hle, Category.assoc,
      Limits.kernelSubobject_arrow_comp, Limits.comp_zero]
  have hfac := congrArg (fun f : (U.generated n : SimplicialObject A) ⟶ U ↦
    f.app (op ⦋m⦌))
      (Subobject.underlyingIso_hom_comp_eq_mk (generated.inclusion U n))
  change (Subobject.mk (generated.inclusion U n)).arrow.app (op ⦋m⦌) ≫ p = 0
  rw [← hfac]
  change ((Subobject.underlyingIso (generated.inclusion U n)).hom.app (op ⦋m⦌) ≫
    (generated.degree U n ⦋m⦌).arrow) ≫ p = 0
  rw [Category.assoc, hdegree, Limits.comp_zero]

set_option backward.isDefEq.respectTransparency false in
private lemma skeleton_comp_eq_zero {m : ℕ} (U : SimplicialObject.Truncated A m)
    (n : ℕ) {T : A} (p : ((Truncated.sk m).obj U).obj (op ⦋n⦌) ⟶ T)
    (hp : ∀ (Delta : (SimplexCategory.Truncated m)ᵒᵖ)
      (theta : (SimplexCategory.Truncated.inclusion m).op.obj Delta ⟶ op ⦋n⦌),
      ((Truncated.sk m).obj U).map theta ≫ p = 0) : p = 0 := by
  apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit
    (SimplexCategory.Truncated.inclusion m).op U (op ⦋n⦌)).hom_ext'
  intro Delta theta
  change ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app Delta ≫
      ((Truncated.sk m).obj U).map theta ≫ p =
    ((SimplexCategory.Truncated.inclusion m).op.leftKanExtensionUnit U).app Delta ≫
      ((Truncated.sk m).obj U).map theta ≫ 0
  simp only [hp Delta theta, Limits.comp_zero]

end

namespace generated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The upper-face normalized Moore subobject of the bounded-degree generated simplicial object
vanishes above the generating bound. -/
@[stacks 017Y "upper-face normalized Moore vanishing companion"]
theorem normalizedMoore.eq_bot_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    NormalizedMooreComplex.objX (U.generated n : SimplicialObject A) m = ⊥ := by
  apply normalizedMoore_eq_bot_of_mono (U.generated n).arrow
  apply generated_arrow_comp_eq_zero
  intro i hi theta
  exact map_comp_projector_eq_zero U m theta (lt_of_le_of_lt hi h)

/-- The upper-face normalized Moore object of a bounded-degree generated simplicial object is
zero above the generating bound. -/
@[stacks 017Y "upper-face normalized Moore zero object above the generating degree"]
theorem normalizedMoore.isZero_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    CategoryTheory.Limits.IsZero
      (NormalizedMooreComplex.objX (U.generated n : SimplicialObject A) m : A) := by
  rw [normalizedMoore.eq_bot_of_lt U h]
  exact (Limits.isZero_zero A).of_iso Subobject.botCoeIsoZero

namespace normalizedMoore.lowerFace

/-- The lower-face normalized Moore subobject of the bounded-degree generated simplicial object
vanishes above the generating bound. -/
@[stacks 017Y "lower-face normalized Moore vanishing above the generating degree"]
theorem eq_bot_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    SimplicialObject.normalizedMoore.lowerFace.subobject
      (U.generated n : SimplicialObject A) m = ⊥ := by
  haveI : Mono
      ((_root_.SimplicialObject.opFunctor.map (U.generated n).arrow).app (op ⦋m⦌)) := by
    change Mono ((U.generated n).arrow.app (op ⦋m⦌))
    infer_instance
  apply normalizedMoore_eq_bot_of_mono
    (_root_.SimplicialObject.opFunctor.map (U.generated n).arrow)
  change (U.generated n).arrow.app (op ⦋m⦌) ≫
    (DoldKan.PInfty (X := _root_.SimplicialObject.opFunctor.obj U)).f m = 0
  apply generated_arrow_comp_eq_zero
  intro i hi theta
  exact map_comp_lowerFace_projector_eq_zero U m theta (lt_of_le_of_lt hi h)

/-- The lower-face normalized Moore object of a bounded-degree generated simplicial object is
zero above the generating bound. -/
@[stacks 017Y "lower-face normalized Moore zero object above the generating degree"]
theorem isZero_of_lt (U : SimplicialObject A) {n m : ℕ} (h : n < m) :
    CategoryTheory.Limits.IsZero
      (SimplicialObject.normalizedMoore.lowerFace.subobject
        (U.generated n : SimplicialObject A) m : A) := by
  rw [eq_bot_of_lt U h]
  exact (Limits.isZero_zero A).of_iso Subobject.botCoeIsoZero

end normalizedMoore.lowerFace

end generated

namespace Truncated

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The upper-face normalized Moore subobject of the simplicial skeleton of an `m`-truncated
object vanishes in every degree strictly greater than `m`. -/
@[stacks 018T "upper-face normalized Moore vanishing companion"]
theorem sk.normalizedMoore.eq_bot_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    NormalizedMooreComplex.objX ((Truncated.sk m).obj U) n = ⊥ := by
  apply normalizedMoore_eq_bot_of_projector_eq_zero
  apply skeleton_comp_eq_zero U n
  intro Delta theta
  exact map_comp_projector_eq_zero _ n theta.unop
    (lt_of_le_of_lt Delta.unop.property h)

/-- The upper-face normalized Moore object of a simplicial skeleton is zero above its truncation
degree. -/
@[stacks 018T "upper-face normalized Moore zero object above a simplicial skeleton"]
theorem sk.normalizedMoore.isZero_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    CategoryTheory.Limits.IsZero
      (NormalizedMooreComplex.objX ((Truncated.sk m).obj U) n : A) := by
  rw [sk.normalizedMoore.eq_bot_of_lt U h]
  exact (Limits.isZero_zero A).of_iso Subobject.botCoeIsoZero

namespace sk.normalizedMoore.lowerFace

/-- The lower-face normalized Moore subobject of the simplicial skeleton of an `m`-truncated object
vanishes in every degree strictly greater than `m`. -/
@[stacks 018T "lower-face normalized Moore vanishing above a simplicial skeleton"]
theorem eq_bot_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    SimplicialObject.normalizedMoore.lowerFace.subobject ((Truncated.sk m).obj U) n = ⊥ := by
  apply normalizedMoore_eq_bot_of_projector_eq_zero
  apply skeleton_comp_eq_zero U n
  intro Delta theta
  exact map_comp_lowerFace_projector_eq_zero _ n theta.unop
    (lt_of_le_of_lt Delta.unop.property h)

/-- The lower-face normalized Moore object of a simplicial skeleton is zero above its truncation
degree. -/
@[stacks 018T "lower-face normalized Moore zero object above a simplicial skeleton"]
theorem isZero_of_lt {m : ℕ} (U : SimplicialObject.Truncated A m)
    {n : ℕ} (h : m < n) :
    CategoryTheory.Limits.IsZero
      (SimplicialObject.normalizedMoore.lowerFace.subobject
        ((Truncated.sk m).obj U) n : A) := by
  rw [eq_bot_of_lt U h]
  exact (Limits.isZero_zero A).of_iso Subobject.botCoeIsoZero

end sk.normalizedMoore.lowerFace

end Truncated

end CategoryTheory.SimplicialObject
