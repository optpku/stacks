/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.ColimitMap

/-!
# Skeleton of a truncated simplicial object concentrated in one degree

This leaf owns the pointwise skeleton coordinates of `Truncated.concentrated B k`, their
structure-map formulas, and their natural assembly in the coefficient object.  It is independent
of biproduct decompositions and category-wide finite-colimit instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.skeleton

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

/-- The costructured arrow represented by an epimorphism `[n] ⟶ [k]`. -/
abbrev topArrow {k n : ℕ} (f : EpiHom ⦋n⦌ ⦋k⦌) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) :=
  CostructuredArrow.mk (Y := op (top k)) f.hom.op

/-- The pointwise colimit diagram computing the degree-`n` skeleton of `concentrated B k`. -/
abbrev diagram (B : A) (k n : ℕ) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) ⥤ A :=
  CostructuredArrow.proj (SimplexCategory.Truncated.inclusion k).op (op ⦋n⦌) ⋙
    concentrated B k

end Internal

/-- The canonical map from the summand indexed by `f : EpiHom ⦋n⦌ ⦋k⦌` into degree `n` of
the skeleton of `concentrated B k`. -/
@[stacks 0190 "skeleton summand inclusion"]
noncomputable def ι (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    B ⟶ (concentrated B k).skeleton.obj (op ⦋n⦌) :=
  topHom B k ≫ colimit.ι (Internal.diagram B k n) (Internal.topArrow f) ≫
    ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionObjIsoColimit
      (concentrated B k) (op ⦋n⦌)).inv

set_option backward.isDefEq.respectTransparency false in
/-- The skeleton summand map is the top-degree unit leg followed by the corresponding
simplicial operator. -/
@[stacks 0190 "skeleton summand map through the unit"]
theorem ι.eq_unit_map (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseSkeleton] (f : EpiHom ⦋n⦌ ⦋k⦌) :
    ι B f =
      topHom B k ≫
        ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
          (concentrated B k)).app (op (top k)) ≫
        (concentrated B k).skeleton.map f.hom.op := by
  unfold ι
  rw [Functor.ι_leftKanExtensionObjIsoColimit_inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A skeleton structure map sends a summand to the partially precomposed epic summand, or to
zero when the composite is not epic. -/
@[stacks 0190 "skeleton structure map on a summand"]
theorem map_ι (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌) :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      (a.precomp f).elim 0 (fun c ↦ ι B c) := by
  classical
  by_cases h : Epi (f ≫ a.hom)
  · show ι B a ≫ (concentrated B k).skeleton.map f.op =
      (a.precomp f).elim 0 (fun c ↦ ι B c)
    simp only [EpiHom.precomp, dif_pos h, Option.elim_some]
    rw [ι.eq_unit_map, ι.eq_unit_map]
    simp only [EpiHom.hom, Category.assoc, op_comp, Functor.map_comp]
  · show ι B a ≫ (concentrated B k).skeleton.map f.op =
      (a.precomp f).elim 0 (fun c ↦ ι B c)
    simp only [EpiHom.precomp, dif_neg h, Option.elim_none]
    rw [ι.eq_unit_map]
    have hcomp :
        (concentrated B k).skeleton.map a.hom.op ≫
            (concentrated B k).skeleton.map f.op =
          (concentrated B k).skeleton.map (f ≫ a.hom).op := by
      rw [op_comp, Functor.map_comp]
    simp only [Category.assoc]
    rw [hcomp]
    cases k with
    | zero =>
      exfalso
      apply h
      rw [SimplexCategory.epi_iff_surjective]
      change Function.Surjective
        (show Fin (n + 1) → Fin 1 from (f ≫ a.hom).toOrderHom)
      exact fun i ↦ ⟨0, Subsingleton.elim _ i⟩
    | succ k =>
      obtain ⟨i, g, hg⟩ := eq_comp_δ_of_not_surjective (f ≫ a.hom)
        (by rwa [← SimplexCategory.epi_iff_surjective])
      let d : op (top (k + 1)) ⟶
          op (⟨⦋k⦌, Nat.le_succ k⟩ : SimplexCategory.Truncated (k + 1)) :=
        (ObjectProperty.homMk (SimplexCategory.δ i)).op
      have hd : (concentrated B (k + 1)).map d = 0 := by
        dsimp [concentrated, concentrated.raw.map, d]
        simp only [dif_pos trivial, dif_neg (Nat.ne_add_one k)]
      have hu := ((SimplexCategory.Truncated.inclusion (k + 1)).op.leftKanExtensionUnit
        (concentrated B (k + 1))).naturality d
      have hz :
          ((SimplexCategory.Truncated.inclusion (k + 1)).op.leftKanExtensionUnit
            (concentrated B (k + 1))).app (op (top (k + 1))) ≫
            (concentrated B (k + 1)).skeleton.map (SimplexCategory.δ i).op = 0 := by
        calc
          _ = (concentrated B (k + 1)).map d ≫
              ((SimplexCategory.Truncated.inclusion (k + 1)).op.leftKanExtensionUnit
                (concentrated B (k + 1))).app
                (op (⟨⦋k⦌, Nat.le_succ k⟩ : SimplexCategory.Truncated (k + 1))) := hu.symm
          _ = 0 := by rw [hd, zero_comp]
      rw [hg, op_comp, Functor.map_comp, ← Category.assoc _ _
        ((concentrated B (k + 1)).skeleton.map g.op), hz, zero_comp, comp_zero]

/-- A skeleton structure map sends an epic composite to its corresponding summand. -/
@[stacks 0190 "skeleton structure map on an epic composite"]
theorem map_ι_of_epi (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    [Epi (f ≫ a.hom)] :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      ι B ⟨f ≫ a.hom, inferInstance⟩ := by
  classical
  simpa only [EpiHom.precomp, dif_pos (inferInstance : Epi (f ≫ a.hom)),
    Option.elim_some] using map_ι B f a

/-- Explicit-proof bridge for the skeleton structure map on an epic composite. -/
@[stacks 0190 "skeleton structure map with an explicit epimorphism proof"]
theorem map_ι_of_epi.explicit (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    (h : Epi (f ≫ a.hom)) :
    ι B a ≫ (concentrated B k).skeleton.map f.op =
      ι B ⟨f ≫ a.hom, h⟩ := by
  letI := h
  exact map_ι_of_epi B f a

/-- A skeleton structure map vanishes on a summand when the corresponding composite is not
epic. -/
@[stacks 0190 "skeleton structure map on a nonepic composite"]
theorem map_ι_of_not_epi (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseSkeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (a : EpiHom ⦋n'⦌ ⦋k⦌)
    (h : ¬ Epi (f ≫ a.hom)) :
    ι B a ≫ (concentrated B k).skeleton.map f.op = 0 := by
  classical
  simpa only [EpiHom.precomp, dif_neg h, Option.elim_none] using map_ι B f a

namespace degree

/-- For fixed `k` and `n`, evaluate the skeleton of the concentrated object in simplicial
degree `n`, functorially in the coefficient object. -/
@[stacks 0190 "degreewise concentrated skeleton functor"]
noncomputable abbrev functor (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] : A ⥤ A :=
  concentrated.functor (A := A) k ⋙ SimplicialObject.Truncated.sk k ⋙
    (evaluation SimplexCategoryᵒᵖ A).obj (op ⦋n⦌)

/-- The degreewise concentrated-skeleton functor has the expected object value. -/
@[simp, stacks 0190 "degreewise concentrated skeleton object formula"]
theorem functor_obj (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k] (B : A) :
    (functor (A := A) k n).obj B =
      ((SimplicialObject.Truncated.sk k).obj (concentrated B k)).obj (op ⦋n⦌) := rfl

/-- The degreewise concentrated-skeleton functor evaluates coefficient morphisms in degree
`n`. -/
@[simp, stacks 0190 "degreewise concentrated skeleton map formula"]
theorem functor_map (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f =
      ((SimplicialObject.Truncated.sk k).map (concentrated.map k f)).app (op ⦋n⦌) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A coefficient morphism commutes with the canonical skeleton summand map. -/
@[stacks 0190 "concentrated skeleton summand naturality"]
theorem ι_naturality {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) {B D : A} (f : B ⟶ D) :
    f ≫ skeleton.ι D a =
      skeleton.ι B a ≫ (functor (A := A) k n).map f := by
  have ht : f ≫ topHom D k = topHom B k ≫ (concentrated.map k f).app (op (top k)) := by
    dsimp [concentrated.map, mapApp, topHom]
    simp only [dif_pos trivial, ← Category.assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
  have hu :
      ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
        (concentrated B k)).app (op (top k)) ≫
          ((SimplicialObject.Truncated.sk k).map (concentrated.map k f)).app (op ⦋k⦌) =
        (concentrated.map k f).app (op (top k)) ≫
          ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
            (concentrated D k)).app (op (top k)) := by
    exact (congr_app
      (((SimplexCategory.Truncated.inclusion k).op.lanUnit).naturality
        (concentrated.map k f)) (op (top k))).symm
  rw [skeleton.ι.eq_unit_map, skeleton.ι.eq_unit_map, functor_map]
  simp only [Category.assoc]
  rw [← Category.assoc f (topHom D k), ht]
  simp only [Category.assoc]
  rw [← Category.assoc ((concentrated.map k f).app (op (top k)))
    (((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
      (concentrated D k)).app (op (top k))), ← hu]
  simp only [Category.assoc]
  exact congrArg
    (fun g ↦ topHom B k ≫
      ((SimplexCategory.Truncated.inclusion k).op.leftKanExtensionUnit
        (concentrated B k)).app (op (top k)) ≫ g)
    (((SimplicialObject.Truncated.sk k).map (concentrated.map k f)).naturality a.hom.op).symm

/-- The canonical skeleton summand map, natural in the coefficient object. -/
@[stacks 0190 "natural concentrated skeleton summand map"]
noncomputable def ι {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) : 𝟭 A ⟶ functor (A := A) k n where
  app B := skeleton.ι B a
  naturality _ _ f := ι_naturality a f

/-- A component of the natural skeleton summand map is the corresponding objectwise map. -/
@[simp, stacks 0190 "natural concentrated skeleton summand component"]
theorem ι_app {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseSkeletons A k]
    (a : EpiHom ⦋n⦌ ⦋k⦌) (B : A) :
    (ι (A := A) a).app B = skeleton.ι B a := rfl

end degree

end concentrated.skeleton

end CategoryTheory.SimplicialObject.Truncated
