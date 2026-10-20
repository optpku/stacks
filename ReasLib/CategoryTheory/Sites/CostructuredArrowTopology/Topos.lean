/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.CostructuredArrowTopology
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.CatCommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cocontinuous comma-site comparisons

This file owns the sheaf-topos comparison for the topology on a costructured
arrow category.  The topology and the continuity of its projection are owned
by `CostructuredArrowTopology`; only the additional comma-to-slice data lives
here.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe uC uD vC vD uA

namespace CategoryTheory.CostructuredArrow.CocontinuousOver

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable (u : C ⥤ D) (V : D)

/-- The canonical functor from the cocontinuous comma site to the target slice site
is cocontinuous whenever `u` is. -/
instance toOver_isCocontinuous [u.IsCocontinuous J K] :
    Functor.IsCocontinuous (CostructuredArrow.toOver u V)
      (cocontinuousOverTopology J u V) (K.over V) := sorry

/-- The projection, the comma-to-slice functor, the original functor, and the slice
forgetful functor form a commutative square of categories: both composites send `(U, ψ)` to
`u.obj U`, so the square commutes on the nose. -/
instance catCommSq :
    CatCommSq (CostructuredArrow.proj u V) (CostructuredArrow.toOver u V) u (Over.forget V) where
  iso := Iso.refl _

@[simp]
theorem catCommSq_iso :
    CatCommSq.iso (CostructuredArrow.proj u V) (CostructuredArrow.toOver u V) u
      (Over.forget V) = Iso.refl _ :=
  rfl

/-- For `V' → V` in `D / V`, the index category of the pointwise right Kan extension along
`(CostructuredArrow.toOver u V).op` at `V'` is equivalent to the index category of the pointwise
right Kan extension along `u.op` at `V'.left` (the equivalence
`ᵘ_{V'}ℐ → ᵘ'_{V'/V}ℐ` in the proof of Lemma 7.28.5). -/
def structuredArrowEquivalence (V' : Over V) :
    StructuredArrow (Opposite.op V') (CostructuredArrow.toOver u V).op ≌
      StructuredArrow (Opposite.op V'.left) u.op :=
  (costructuredArrowOpEquivalence (CostructuredArrow.toOver u V) V').symm.trans
    ((CostructuredArrow.costructuredArrowToOverEquivalence u V').op.trans
      (costructuredArrowOpEquivalence u V'.left))

/-- The presheaf-level comparison behind Lemma 7.28.5 (5): restricting along the comma
projection and then right Kan extending along `toOver` agrees with right Kan extending along `u`
and then restricting to `D / V`. Componentwise it is the comparison of the two pointwise limits
along `structuredArrowEquivalence`. -/
def ranComparison
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F] :
    (Functor.whiskeringLeft _ _ (Type uA)).obj (CostructuredArrow.proj u V).op ⋙
        (CostructuredArrow.toOver u V).op.ran ≅
      u.op.ran ⋙ (Functor.whiskeringLeft _ _ (Type uA)).obj (Over.forget V).op :=
  NatIso.ofComponents (fun G ↦ NatIso.ofComponents (fun V' ↦
      (CostructuredArrow.toOver u V).op.ranObjObjIsoLimit _ V' ≪≫
        HasLimit.isoOfEquivalence (structuredArrowEquivalence u V V'.unop)
          (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; sorry)) ≪≫
        (u.op.ranObjObjIsoLimit G (Opposite.op V'.unop.left)).symm)
      (by intros; sorry)) (by intros; sorry)

/-- The inverse of `ranComparison` is the base-change (mate) transformation of the
on-the-nose commutative square `catCommSq` with respect to the two right Kan extension
adjunctions. -/
theorem ranComparison_inv_eq_mate
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F] :
    (ranComparison u V).inv =
      (mateEquiv (u.op.ranAdjunction (Type uA))
        ((CostructuredArrow.toOver u V).op.ranAdjunction (Type uA))
        (TwoSquare.mk
          ((Functor.whiskeringLeft _ _ (Type uA)).obj (Over.forget V).op)
          ((Functor.whiskeringLeft _ _ (Type uA)).obj u.op)
          ((Functor.whiskeringLeft _ _ (Type uA)).obj (CostructuredArrow.toOver u V).op)
          ((Functor.whiskeringLeft _ _ (Type uA)).obj (CostructuredArrow.proj u V).op)
          (𝟙 _))).natTrans := sorry

/-- Lemma 7.28.5 (0D5R) (5): `f'_* j⁻¹ ≅ j_V⁻¹ f_*`, where `j⁻¹` is restriction along the
comma projection, `f'_*` and `f_*` are the cocontinuous direct images of `toOver u V` and `u`,
and `j_V⁻¹` is restriction to `D / V`. It is the sheaf-level form of `ranComparison`. -/
@[stacks 0D5R]
def directImageComparison
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F] :
    Functor.sheafPushforwardContinuous (CostructuredArrow.proj u V) (Type uA)
        (cocontinuousOverTopology J u V) J ⋙
      Functor.sheafPushforwardCocontinuous (CostructuredArrow.toOver u V) (Type uA)
        (cocontinuousOverTopology J u V) (K.over V) ≅
    Functor.sheafPushforwardCocontinuous u (Type uA) J K ⋙
      Functor.sheafPushforwardContinuous (Over.forget V) (Type uA) (K.over V) K :=
  NatIso.ofComponents
    (fun G ↦ (fullyFaithfulSheafToPresheaf (K.over V) (Type uA)).preimageIso
      ((ranComparison u V).app G.obj))
    (by intros; sorry)

@[simp]
theorem directImageComparison_hom_app_hom
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    (G : Sheaf J (Type uA)) :
    ((directImageComparison J K u V).hom.app G).hom = (ranComparison u V).hom.app G.obj :=
  rfl

@[simp]
theorem directImageComparison_inv_app_hom
    [u.IsCocontinuous J K]
    [∀ F : Cᵒᵖ ⥤ Type uA, u.op.HasPointwiseRightKanExtension F]
    [∀ F : (CostructuredArrow u V)ᵒᵖ ⥤ Type uA,
      (CostructuredArrow.toOver u V).op.HasPointwiseRightKanExtension F]
    (G : Sheaf J (Type uA)) :
    ((directImageComparison J K u V).inv.app G).hom = (ranComparison u V).inv.app G.obj :=
  rfl

end CategoryTheory.CostructuredArrow.CocontinuousOver
