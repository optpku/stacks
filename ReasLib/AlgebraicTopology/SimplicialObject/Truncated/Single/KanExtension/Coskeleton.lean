/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Single.Functor
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise
public import ReasLib.AlgebraicTopology.SimplexCategory.EpiMono
public import ReasLib.CategoryTheory.Functor.RightKanExtension.LimitMap

/-!
# Coskeleton of a truncated simplicial object concentrated in one degree

This leaf owns the pointwise coskeleton coordinates of `Truncated.concentrated B k`, their
structure-map formulas, and their natural assembly in the coefficient object.  It is independent
of biproduct decompositions and category-wide finite-limit instances.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open SimplexCategory
open scoped SimplexCategory.Truncated Simplicial

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Truncated

variable {A : Type u} [Category.{v} A]

namespace concentrated.coskeleton

variable [HasZeroObject A] [HasZeroMorphisms A]

namespace Internal

/-- The structured arrow represented by a monomorphism `[k] ⟶ [n]`. -/
abbrev topArrow {k n : ℕ} (f : MonoHom ⦋k⦌ ⦋n⦌) :
    StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op :=
  StructuredArrow.mk (Y := op (top k)) f.hom.op

/-- The pointwise limit diagram computing the degree-`n` coskeleton of `concentrated B k`. -/
abbrev diagram (B : A) (k n : ℕ) :
    StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op ⥤ A :=
  StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion k).op ⋙
    concentrated B k

end Internal

/-- The canonical projection from degree `n` of the coskeleton of `concentrated B k` to the
factor indexed by `f : MonoHom ⦋k⦌ ⦋n⦌`. -/
@[stacks 0190 "coskeleton factor projection"]
noncomputable def π (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    (concentrated B k).coskeleton.obj (op ⦋n⦌) ⟶ B :=
  (Functor.RightKanExtension.objIsoLimit
      (SimplexCategory.Truncated.inclusion k).op
      (concentrated B k) (op ⦋n⦌)).hom ≫
    limit.π (Internal.diagram B k n) (Internal.topArrow f) ≫ topInv B k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The coskeleton projection is the corresponding simplicial operator followed by the
top-degree counit leg. -/
@[stacks 0190 "coskeleton projection through the counit"]
theorem π.eq_map_counit (B : A) {k n : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton] (f : MonoHom ⦋k⦌ ⦋n⦌) :
    π B f =
      (concentrated B k).coskeleton.map f.hom.op ≫
        ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
          (concentrated B k)).app (op (top k)) ≫
        topInv B k := by
  dsimp only [π, Functor.RightKanExtension.objIsoLimit, Internal.diagram]
  rw [← Category.assoc,
    Functor.RightExtension.IsPointwiseRightKanExtensionAt.isoLimit_hom_π]
  exact Category.assoc _ _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A coskeleton structure map sends a projection to the partially postcomposed monic factor,
or to zero when the composite is not monic. -/
@[stacks 0190 "coskeleton structure map on a projection"]
theorem map_π (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌) :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      (b.postcomp f).elim 0 (fun c ↦ π B c) := by
  classical
  by_cases h : Mono (b.hom ≫ f)
  · simp only [MonoHom.postcomp, dif_pos h, Option.elim_some, π.eq_map_counit, MonoHom.hom,
      op_comp, Functor.map_comp, Category.assoc]
  · simp only [MonoHom.postcomp, dif_neg h, Option.elim_none]
    rw [π.eq_map_counit]
    have hzero :
        (concentrated B k).coskeleton.map (b.hom ≫ f).op ≫
          ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
            (concentrated B k)).app (op (top k)) = 0 := by
      cases k with
      | zero =>
        exact (h (SimplexCategory.mono_iff_injective.mpr
          (fun (x y : Fin 1) _ ↦ Subsingleton.elim x y))).elim
      | succ k =>
        obtain ⟨i, g, hg⟩ := eq_σ_comp_of_not_injective (b.hom ≫ f)
          (fun hinj ↦ h (SimplexCategory.mono_iff_injective.mpr hinj))
        let s : top (k + 1) ⟶
            (⟨⦋k⦌, Nat.le_succ k⟩ : SimplexCategory.Truncated (k + 1)) :=
          SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i)
        have hs : (concentrated B (k + 1)).map s.op = 0 := by
          simp only [concentrated, concentrated.raw.map, s, Nat.ne_add_one, dite_false]
        have hc :=
          ((SimplexCategory.Truncated.inclusion (k + 1)).op.rightKanExtensionCounit
            (concentrated B (k + 1))).naturality s.op
        change (concentrated B (k + 1)).coskeleton.map (SimplexCategory.σ i).op ≫
            ((SimplexCategory.Truncated.inclusion (k + 1)).op.rightKanExtensionCounit
              (concentrated B (k + 1))).app (op (top (k + 1))) = _ at hc
        rw [hs, comp_zero] at hc
        rw [hg, op_comp, Functor.map_comp, Category.assoc, hc, comp_zero]
    calc
      _ = ((concentrated B k).coskeleton.map (b.hom ≫ f).op ≫
          ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
            (concentrated B k)).app (op (top k))) ≫ topInv B k := by
        rw [op_comp, Functor.map_comp, Category.assoc, Category.assoc]
      _ = 0 := by rw [hzero, zero_comp]

/-- A coskeleton structure map sends a monic composite to its corresponding projection. -/
@[stacks 0190 "coskeleton structure map on a monic composite"]
theorem map_π_of_mono (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    [Mono (b.hom ≫ f)] :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      π B ⟨b.hom ≫ f, inferInstance⟩ := by
  classical
  simpa only [MonoHom.postcomp, dif_pos (inferInstance : Mono (b.hom ≫ f)),
    Option.elim_some] using map_π B f b

/-- Explicit-proof bridge for the coskeleton structure map on a monic composite. -/
@[stacks 0190 "coskeleton structure map with an explicit monomorphism proof"]
theorem map_π_of_mono.explicit (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    (h : Mono (b.hom ≫ f)) :
    (concentrated B k).coskeleton.map f.op ≫ π B b =
      π B ⟨b.hom ≫ f, h⟩ := by
  letI := h
  exact map_π_of_mono B f b

/-- A coskeleton structure map followed by a factor projection vanishes when the corresponding
composite is not monic. -/
@[stacks 0190 "coskeleton structure map on a nonmonic composite"]
theorem map_π_of_not_mono (B : A) {k n n' : ℕ}
    [(concentrated B k).HasPointwiseCoskeleton]
    (f : ⦋n⦌ ⟶ ⦋n'⦌) (b : MonoHom ⦋k⦌ ⦋n⦌)
    (h : ¬ Mono (b.hom ≫ f)) :
    (concentrated B k).coskeleton.map f.op ≫ π B b = 0 := by
  classical
  simpa only [MonoHom.postcomp, dif_neg h, Option.elim_none] using map_π B f b

namespace degree

/-- For fixed `k` and `n`, evaluate the coskeleton of the concentrated object in simplicial
degree `n`, functorially in the coefficient object. -/
@[stacks 0190 "degreewise concentrated coskeleton functor"]
noncomputable abbrev functor (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] : A ⥤ A :=
  concentrated.functor (A := A) k ⋙ SimplicialObject.Truncated.cosk k ⋙
    (evaluation SimplexCategoryᵒᵖ A).obj (op ⦋n⦌)

/-- The degreewise concentrated-coskeleton functor has the expected object value. -/
@[simp, stacks 0190 "degreewise concentrated coskeleton object formula"]
theorem functor_obj (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k] (B : A) :
    (functor (A := A) k n).obj B =
      ((SimplicialObject.Truncated.cosk k).obj (concentrated B k)).obj (op ⦋n⦌) := rfl

/-- The degreewise concentrated-coskeleton functor evaluates coefficient morphisms in degree
`n`. -/
@[simp, stacks 0190 "degreewise concentrated coskeleton map formula"]
theorem functor_map (k n : ℕ)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f =
      ((SimplicialObject.Truncated.cosk k).map (concentrated.map k f)).app (op ⦋n⦌) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A coefficient morphism commutes with the canonical coskeleton factor map. -/
@[stacks 0190 "concentrated coskeleton factor naturality"]
theorem π_naturality {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) {B D : A} (f : B ⟶ D) :
    (functor (A := A) k n).map f ≫ coskeleton.π D b =
      coskeleton.π B b ≫ f := by
  let α : (concentrated B k).coskeleton ⟶ (concentrated D k).coskeleton :=
    (SimplicialObject.Truncated.cosk k).map (concentrated.map k f)
  have hc := congr_app
    ((SimplexCategory.Truncated.inclusion k).op.ranCounit.naturality
      (concentrated.map k f)) (op (top k))
  change α.app (op ⦋k⦌) ≫
      ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
        (concentrated D k)).app (op (top k)) =
    ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
      (concentrated B k)).app (op (top k)) ≫
        (concentrated.map k f).app (op (top k)) at hc
  have ht : (concentrated.map k f).app (op (top k)) ≫ topInv D k =
      topInv B k ≫ f := by
    simp only [concentrated.map, mapApp, topInv, dite_true, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  change α.app (op ⦋n⦌) ≫ coskeleton.π D b = coskeleton.π B b ≫ f
  rw [coskeleton.π.eq_map_counit, coskeleton.π.eq_map_counit]
  calc
    _ = (concentrated B k).coskeleton.map b.hom.op ≫
        (α.app (op ⦋k⦌) ≫
          ((SimplexCategory.Truncated.inclusion k).op.rightKanExtensionCounit
            (concentrated D k)).app (op (top k))) ≫ topInv D k := by
      rw [← α.naturality_assoc]
      simp only [Category.assoc]
    _ = _ := by rw [hc, Category.assoc, ht, Category.assoc, Category.assoc]

/-- The canonical coskeleton factor map, natural in the coefficient object. -/
@[stacks 0190 "natural concentrated coskeleton factor map"]
noncomputable def π {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) : functor (A := A) k n ⟶ 𝟭 A where
  app B := coskeleton.π B b
  naturality _ _ f := π_naturality b f

/-- A component of the natural coskeleton factor map is the corresponding objectwise map. -/
@[simp, stacks 0190 "natural concentrated coskeleton factor component"]
theorem π_app {k n : ℕ}
    [SimplicialObject.Truncated.HasPointwiseCoskeletons A k]
    (b : MonoHom ⦋k⦌ ⦋n⦌) (B : A) :
    (π (A := A) b).app B = coskeleton.π B b := rfl

end degree

end concentrated.coskeleton

end CategoryTheory.SimplicialObject.Truncated
