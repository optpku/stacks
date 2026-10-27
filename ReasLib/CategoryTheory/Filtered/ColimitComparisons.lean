/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Products
public import ReasLib.CategoryTheory.Filtered.CommonSuccessors
public import ReasLib.CategoryTheory.Filtered.SpanCocones

/-!
# Colimit comparison maps under weak filteredness hypotheses

This module gives computation and surjectivity APIs for canonical colimit comparison maps under
the weakest object- or span-level hypotheses needed by the corresponding statements.
-/

@[expose] public section

open CategoryTheory

universe w v u

noncomputable section

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]

namespace prodComparison

set_option backward.isDefEq.respectTransparency false in
/-- The first coordinate of the binary-product comparison on a colimit representative. -/
theorem colim.ι.fst
    [Small.{w} I] (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).1 =
      colimit.ι M k ((prod.fst : M ⨯ N ⟶ M).app k x) := by
  calc
    _ = (prod.fst : colimit M ⨯ colimit N ⟶ colimit M)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) :=
      ConcreteCategory.congr_hom
        (Types.binaryProductIso_hom_comp_fst (colimit M) (colimit N)) _
    _ = colim.map (prod.fst : M ⨯ N ⟶ M) (colimit.ι (M ⨯ N) k x) :=
      ConcreteCategory.congr_hom (prodComparison_fst colim M N) _
    _ = _ := ConcreteCategory.congr_hom (colimit.ι_map (prod.fst : M ⨯ N ⟶ M) k) x

set_option backward.isDefEq.respectTransparency false in
/-- The second coordinate of the binary-product comparison on a colimit representative. -/
theorem colim.ι.snd
    [Small.{w} I] (M N : I ⥤ Type w) (k : I) (x : (M ⨯ N).obj k) :
    ((Types.binaryProductIso (colimit M) (colimit N)).hom
      (prodComparison colim M N (colimit.ι (M ⨯ N) k x))).2 =
      colimit.ι N k ((prod.snd : M ⨯ N ⟶ N).app k x) := by
  calc
    _ = (prod.snd : colimit M ⨯ colimit N ⟶ colimit N)
        (prodComparison colim M N (colimit.ι (M ⨯ N) k x)) :=
      ConcreteCategory.congr_hom
        (Types.binaryProductIso_hom_comp_snd (colimit M) (colimit N)) _
    _ = colim.map (prod.snd : M ⨯ N ⟶ N) (colimit.ι (M ⨯ N) k x) :=
      ConcreteCategory.congr_hom (prodComparison_snd colim M N) _
    _ = _ := ConcreteCategory.congr_hom (colimit.ι_map (prod.snd : M ⨯ N ⟶ N) k) x

/-- Common successors make the binary-product comparison for `Type`-valued colimits
surjective. -/
theorem colim.surjective
    [Small.{w} I] [HasCommonSuccessors I] (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := by
  intro z
  obtain ⟨i, x, hx⟩ := Types.jointly_surjective'
    (((Types.binaryProductIso (colimit M) (colimit N)).hom z).1)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective'
    (((Types.binaryProductIso (colimit M) (colimit N)).hom z).2)
  obtain ⟨s⟩ := HasCommonSuccessors.nonempty i j
  refine ⟨colimit.ι (M ⨯ N) s.obj
    (FunctorToTypes.prodMk (M.map s.left x) (N.map s.right y)), ?_⟩
  apply injective_of_mono (Types.binaryProductIso (colimit M) (colimit N)).hom
  apply _root_.Prod.ext
  · show ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) s.obj
          (FunctorToTypes.prodMk (M.map s.left x) (N.map s.right y))))).1 = _
    rw [colim.ι.fst, FunctorToTypes.prodMk_fst, colimit.w_apply, hx]
  · show ((Types.binaryProductIso (colimit M) (colimit N)).hom
        (prodComparison colim M N (colimit.ι (M ⨯ N) s.obj
          (FunctorToTypes.prodMk (M.map s.left x) (N.map s.right y))))).2 = _
    rw [colim.ι.snd, FunctorToTypes.prodMk_snd, colimit.w_apply, hy]

/-- Explicit-hypothesis form of surjectivity of the binary-product colimit comparison. -/
@[stacks 09WQ "surjectivity of binary-product colimit comparison"]
theorem colim.surjective_of_commonSuccessors
    [Small.{w} I]
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (M N : I ⥤ Type w) :
    Function.Surjective (prodComparison colim M N) := by
  letI : HasCommonSuccessors I := ⟨fun i j => by
    obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hObj i j
    exact ⟨⟨k, f, g⟩⟩⟩
  exact colim.surjective M N

end prodComparison

end CategoryTheory.Limits

namespace AddCommGrpCat

open CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable [Small.{w} I]

/-- The canonical comparison from the colimit of the underlying sets to the underlying set of
the additive colimit. -/
@[stacks 09WR "underlying-set comparison for additive colimits"]
noncomputable def colimitComparison (M : I ⥤ AddCommGrpCat.{w}) :
    colimit (M ⋙ forget AddCommGrpCat) ⟶
      (forget AddCommGrpCat).obj (colimit M) :=
  colimit.post M (forget AddCommGrpCat)

namespace colimitComparison

variable {M : I ⥤ AddCommGrpCat.{w}}

/-- The additive-colimit comparison agrees with the additive colimit injection on every
diagram stage. -/
@[reassoc (attr := simp)]
theorem ι (i : I) :
    colimit.ι (M ⋙ forget AddCommGrpCat) i ≫ colimitComparison M =
      (forget AddCommGrpCat).map (colimit.ι M i) :=
  colimit.ι_post M (forget AddCommGrpCat) i

/-- Elementwise computation of the additive-colimit comparison on a stage representative. -/
@[simp]
theorem ι_apply (i : I) (x : M.obj i) :
    colimitComparison M (colimit.ι (M ⋙ forget AddCommGrpCat) i x) =
      colimit.ι M i x :=
  ConcreteCategory.congr_hom (ι (M := M) i) x

/-- Naturality of the additive-colimit comparison in the additive diagram. -/
@[reassoc]
theorem naturality {N : I ⥤ AddCommGrpCat.{w}} (α : M ⟶ N) :
    colim.map (Functor.whiskerRight α (forget AddCommGrpCat)) ≫ colimitComparison N =
      colimitComparison M ≫ (forget AddCommGrpCat).map (colim.map α) :=
  (colimit.map_post α (forget AddCommGrpCat)).symm

/-- For a nonempty index category with common successors, the canonical map from the colimit of
the underlying sets to the underlying set of the additive colimit is surjective. -/
@[stacks 09WR "surjectivity of the additive colimit comparison"]
theorem surjective
    [Nonempty I] [HasCommonSuccessors I] :
    Function.Surjective (colimitComparison M) := by
  -- The elements represented at a single stage form a subgroup: common successors
  -- let us add representatives, and nonemptiness supplies a representative of zero.
  let S : AddSubgroup (colimit M : AddCommGrpCat.{w}) :=
    { carrier := {x | ∃ (i : I) (y : M.obj i), colimit.ι M i y = x}
      zero_mem' := by
        obtain ⟨i⟩ := ‹Nonempty I›
        exact ⟨i, 0, map_zero (colimit.ι M i).hom⟩
      add_mem' := by
        rintro a b ⟨i, x, rfl⟩ ⟨j, y, rfl⟩
        obtain ⟨s⟩ := HasCommonSuccessors.nonempty i j
        refine ⟨s.obj, M.map s.left x + M.map s.right y, ?_⟩
        rw [map_add (colimit.ι M s.obj).hom, colimit.w_apply, colimit.w_apply]
      neg_mem' := by
        rintro a ⟨i, x, rfl⟩
        exact ⟨i, -x, map_neg (colimit.ι M i).hom x⟩ }
  let c : Cocone M :=
    { pt := of S
      ι :=
        { app i := ofHom ((colimit.ι M i).hom.codRestrict S (fun x => ⟨i, x, rfl⟩))
          naturality i j f := by
            ext x
            apply Subtype.ext
            exact ConcreteCategory.congr_hom (colimit.w M f) x } }
  have h : colimit.desc M c ≫ ofHom S.subtype = 𝟙 (colimit M) := by
    apply colimit.hom_ext
    intro i
    rw [colimit.ι_desc_assoc, Category.comp_id]
    rfl
  intro x
  have hx : (colimit.desc M c x : (colimit M : AddCommGrpCat.{w})) = x :=
    ConcreteCategory.congr_hom h x
  obtain ⟨i, y, hy⟩ := (colimit.desc M c x).property
  refine ⟨colimit.ι (M ⋙ forget AddCommGrpCat) i y, ?_⟩
  rw [ι_apply, hy, hx]

/-- Explicit-hypothesis form of surjectivity of the set-to-abelian-group colimit comparison. -/
@[stacks 09WR "surjectivity of the set-to-abelian-group colimit comparison"]
theorem surjective_of_commonSuccessors
    (hObj : ∀ i j : I, ∃ k : I, Nonempty (i ⟶ k) ∧ Nonempty (j ⟶ k))
    (hI : Nonempty I) :
    Function.Surjective (colimitComparison M) := by
  letI : Nonempty I := hI
  letI : HasCommonSuccessors I := ⟨fun i j => by
    obtain ⟨k, ⟨f⟩, ⟨g⟩⟩ := hObj i j
    exact ⟨⟨k, f, g⟩⟩⟩
  exact surjective

end colimitComparison

end AddCommGrpCat

namespace CategoryTheory.Limits

variable {I : Type u} [Category.{v} I]
variable [Small.{w} I]

/-- With commuting cocones on spans, equality in a colimit of types is witnessed at a common
successor, without any equalization hypothesis on parallel arrows. -/
theorem Types.colimit_eq_of_hasSpanCocones [HasSpanCocones I]
    (F : I ⥤ Type w) {i j : I} {x : F.obj i} {y : F.obj j}
    (h : colimit.ι F i x = colimit.ι F j y) :
    ∃ (k : I) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  have key : ∀ (a b : Σ i, F.obj i), Relation.EqvGen F.ColimitTypeRel a b →
      ∃ (k : I) (f : a.1 ⟶ k) (g : b.1 ⟶ k), F.map f a.2 = F.map g b.2 := by
    intro a b hab
    induction hab with
    | rel a b hab =>
        obtain ⟨f, hf⟩ := hab
        exact ⟨b.1, f, 𝟙 _, by simpa using hf.symm⟩
    | refl a => exact ⟨a.1, 𝟙 _, 𝟙 _, rfl⟩
    | symm a b _ ih =>
        obtain ⟨k, f, g, hfg⟩ := ih
        exact ⟨k, g, f, hfg.symm⟩
    | trans a b c _ _ hab hbc =>
        obtain ⟨k, f, g, hfg⟩ := hab
        obtain ⟨l, f', g', hfg'⟩ := hbc
        obtain ⟨s⟩ := HasSpanCocones.nonempty g f'
        refine ⟨s.pt, f ≫ s.inl, g' ≫ s.inr, ?_⟩
        calc
          F.map (f ≫ s.inl) a.2 = F.map s.inl (F.map f a.2) := by simp
          _ = F.map s.inl (F.map g b.2) := congrArg _ hfg
          _ = F.map (g ≫ s.inl) b.2 := by simp
          _ = F.map (f' ≫ s.inr) b.2 := by rw [s.condition]
          _ = F.map s.inr (F.map f' b.2) := by simp
          _ = F.map s.inr (F.map g' c.2) := congrArg _ hfg'
          _ = F.map (g' ≫ s.inr) c.2 := by simp
  exact key _ _ (Types.colimit_eq h)

set_option backward.isDefEq.respectTransparency false in
/-- If every span in the index category has a commuting cocone, its `Type`-valued colimit
functor preserves monomorphisms. -/
@[stacks 09WT "Type-valued colimits preserve objectwise injectivity"]
instance colim.preservesMonomorphisms_of_hasSpanCocones
    [HasSpanCocones I] :
    (colim : (I ⥤ Type w) ⥤ Type w).PreservesMonomorphisms where
  preserves {M N} α _ := by
    apply (mono_iff_injective _).2
    intro x y hxy
    obtain ⟨i, x, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective' y
    have h : colimit.ι N i (α.app i x) = colimit.ι N j (α.app j y) := by
      calc
        _ = colim.map α (colimit.ι M i x) :=
          (ConcreteCategory.congr_hom (colimit.ι_map α i) x).symm
        _ = colim.map α (colimit.ι M j y) := hxy
        _ = _ := ConcreteCategory.congr_hom (colimit.ι_map α j) y
    obtain ⟨k, f, g, hfg⟩ := Types.colimit_eq_of_hasSpanCocones N h
    apply Types.colimit_sound' f g
    apply (mono_iff_injective (α.app k)).1 inferInstance
    simpa only [NatTrans.naturality_apply] using hfg

end CategoryTheory.Limits
