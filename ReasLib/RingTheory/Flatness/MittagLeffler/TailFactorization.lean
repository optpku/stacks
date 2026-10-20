/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.TailFactorization.HomInverseSystem
public import ReasLib.RingTheory.Flatness.MittagLeffler

/-!
# Tail factorization and Hom criteria for module diagrams

This file compares categorical tail factorization with the all-target and product-target Hom
Mittag-Leffler conditions for module diagrams over an arbitrary ring.
-/

@[expose] public section

open CategoryTheory

universe u v w x

private theorem tailFactorization_of_productHom
    {R : Type u} [Ring R] {I : Type v} [Category.{w} I]
    {F : I ⥤ ModuleCat.{max v x} R}
    (hF : (F.homInverseSystem
      (ModuleCat.of.{max v x} R
        ((s : I) → (F.obj s : Type (max v x))))).IsMittagLeffler) :
    F.HasTailFactorization := by
  classical
  let N := ModuleCat.of.{max v x} R
    ((s : I) → (F.obj s : Type (max v x)))
  intro i
  obtain ⟨jop, f, hf⟩ := hF (Opposite.op i)
  let j := jop.unop
  let insj : F.obj j ⟶ N :=
    ModuleCat.ofHom (LinearMap.single R
      (fun s : I ↦ (F.obj s : Type (max v x))) j)
  let projj : N ⟶ F.obj j := ModuleCat.ofHom (LinearMap.proj j)
  have hins_proj : insj ≫ projj = 𝟙 (F.obj j) := by
    apply ModuleCat.hom_ext
    simpa [insj, projj] using
      (LinearMap.proj_comp_single_same R
        (fun s : I ↦ (F.obj s : Type (max v x))) j)
  refine ⟨j, f.unop, fun k g ↦ ?_⟩
  have hmem : F.map f.unop ≫ insj ∈
      Set.range (ConcreteCategory.hom ((F.homInverseSystem N).map f)) := by
    refine ⟨insj, ?_⟩
    change (F.map f.unop).op.unop ≫ insj = F.map f.unop ≫ insj
    rw [Quiver.Hom.unop_op]
  obtain ⟨q, hq⟩ := hf g.op hmem
  have hq' : F.map g ≫ q = F.map f.unop ≫ insj := by
    change (F.map g).op.unop ≫ q = F.map f.unop ≫ insj at hq
    simpa only [Quiver.Hom.unop_op] using hq
  refine ⟨q ≫ projj, ?_⟩
  calc
    F.map f.unop = (F.map f.unop ≫ insj) ≫ projj := by
      rw [Category.assoc, hins_proj, Category.comp_id]
    _ = (F.map g ≫ q) ≫ projj := by rw [hq']
    _ = F.map g ≫ (q ≫ projj) := Category.assoc _ _ _

namespace Module.IsMittagLefflerDirectedSystem

variable {R : Type u} [Ring R]
variable {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {F : I ⥤ ModuleCat.{max v w} R}

/-- A Mittag-Leffler directed system has tail factorization. -/
@[stacks 059E "directed system"]
theorem hasTailFactorization (hF : IsMittagLefflerDirectedSystem F) :
    F.HasTailFactorization :=
  tailFactorization_of_productHom
    (hF.homMittagLeffler
      (ModuleCat.of.{max v w} R
        ((s : I) → (F.obj s : Type (max v w)))))

/-- A module diagram is Mittag-Leffler exactly when its stages are finitely presented and it
has tail factorization. -/
@[stacks 059E "tail factorization criterion"]
theorem iff_tailFactorization (F : I ⥤ ModuleCat.{max v w} R) :
    IsMittagLefflerDirectedSystem F ↔
      (∀ i, Module.FinitePresentation R (F.obj i)) ∧ F.HasTailFactorization := by
  constructor
  · intro hF
    exact ⟨hF.finitePresentation, hF.hasTailFactorization⟩
  · rintro ⟨hfp, htail⟩
    exact ⟨hfp, htail.homMittagLeffler⟩

end Module.IsMittagLefflerDirectedSystem

namespace ModuleCat

variable {R : Type u} [Ring R]
variable {I : Type v} [Category.{w} I]

/-- The Hom inverse system with target the product of all stages is Mittag-Leffler. -/
@[stacks 059E "product Hom criterion"]
abbrev ProductHomMittagLeffler (F : I ⥤ ModuleCat.{max v x} R) : Prop :=
  (F.homInverseSystem
    (ModuleCat.of.{max v x} R
      ((s : I) → (F.obj s : Type (max v x))))).IsMittagLeffler

/-- The product-target Hom test detects tail factorization. -/
@[stacks 059E "product Hom criterion"]
theorem ProductHomMittagLeffler.tailFactorization {F : I ⥤ ModuleCat.{max v x} R}
    (hF : ProductHomMittagLeffler F) : F.HasTailFactorization :=
  tailFactorization_of_productHom hF

/-- Product-target Hom Mittag-Lefflerness is equivalent to tail factorization. -/
@[stacks 059E "product Hom criterion iff"]
theorem ProductHomMittagLeffler.iff_tailFactorization
    (F : I ⥤ ModuleCat.{max v x} R) :
    ProductHomMittagLeffler F ↔ F.HasTailFactorization :=
  ⟨ProductHomMittagLeffler.tailFactorization,
    fun hF ↦ hF.homInverseSystem
      (ModuleCat.of.{max v x} R ((s : I) → (F.obj s : Type (max v x))))⟩

end ModuleCat

namespace CategoryTheory.Functor.HomMittagLeffler

variable {R : Type u} [Ring R]
variable {I : Type v} [Category.{w} I]

/-- All-target Hom Mittag-Lefflerness is equivalent to tail factorization for module
diagrams. -/
@[stacks 059E "Hom criterion iff"]
theorem iff_tailFactorization (F : I ⥤ ModuleCat.{max v x} R) :
    F.HomMittagLeffler ↔ F.HasTailFactorization := by
  constructor
  · intro hF
    exact ModuleCat.ProductHomMittagLeffler.tailFactorization
      (hF (ModuleCat.of.{max v x} R
        ((s : I) → (F.obj s : Type (max v x)))))
  · exact CategoryTheory.Functor.HasTailFactorization.homMittagLeffler

/-- All-target Hom Mittag-Lefflerness is equivalent to its single product-target test. -/
@[stacks 059E "product detection"]
theorem iff_product (F : I ⥤ ModuleCat.{max v x} R) :
    F.HomMittagLeffler ↔ ModuleCat.ProductHomMittagLeffler F :=
  (iff_tailFactorization F).trans
    (ModuleCat.ProductHomMittagLeffler.iff_tailFactorization F).symm

end CategoryTheory.Functor.HomMittagLeffler
