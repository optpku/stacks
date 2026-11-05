/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Degreewise split short exact triangles in the derived category

This file separates the canonical change-of-functor comparison from the
noncanonical uniqueness-up-to-isomorphism statement for distinguished
triangles.  Only the former is exposed as concrete `Iso` data.
-/

open CategoryTheory
open CategoryTheory.Pretriangulated
open ComplexShape

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.ShortExact

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical comparison between first passing a degreewise split triangle
to the homotopy category and then applying `Qh`, and applying `Q` directly. -/
@[stacks 0154]
noncomputable def degreewiseSplitImageIso
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    _root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ) ≅
      _root_.DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.triangleOfDegreewiseSplit S σ) :=
  (Functor.mapTriangleCompIso
      (HomotopyCategory.quotient 𝒜 (up ℤ)) _root_.DerivedCategory.Qh).symm.app _ ≪≫
    (Functor.mapTriangleIso (_root_.DerivedCategory.quotientCompQhIso 𝒜)).app _

open CategoryTheory.Category CategoryTheory.Preadditive
  CochainComplex CochainComplex.HomComplex HomologicalComplex in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a degreewise split short exact sequence, the canonical derived boundary
is the image of the connecting map computed from the chosen splitting.
Unlike an abstract isomorphism of triangles, this formula fixes all three
vertices and identifies the boundary used by the canonical delta-functor. -/
@[stacks 0154]
theorem triangleOfSESδ_eq_of_degreewiseSplit
    {S : ShortComplex (CochainComplex 𝒜 ℤ)} (hS : S.ShortExact)
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    _root_.DerivedCategory.triangleOfSESδ hS =
      _root_.DerivedCategory.Q.map (CochainComplex.homOfDegreewiseSplit S σ) ≫
        (_root_.DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app S.X₁ := by
  let γ : Cochain S.X₂ (S.X₁⟦(1 : ℤ)⟧) (-1) :=
    Cochain.mk fun p q hpq =>
      (σ p).r ≫ (S.X₁.shiftFunctorObjXIso 1 q p (by lia)).inv
  have H : Homotopy
      (mappingCone.descShortComplex S ≫ homOfDegreewiseSplit S σ)
      (mappingCone.triangle S.f).mor₃ :=
    mappingCone.descHomotopy S.f _ _ 0 γ (by
      ext p q hpq
      have hr := (σ p).f_r
      dsimp at hr
      simp [γ, mappingCone.descShortComplex, ← Category.assoc, hr]) (by
      ext p
      have hr := (σ (p + 1)).f_r
      have hi := (σ p).id
      dsimp at hr hi
      simp [γ, δ_v (-1) 0 (by simp) _ p p (by simp) (p - 1) (p + 1)
        (by lia) (by lia), homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit,
        ← Category.assoc]
      simp only [Category.assoc, XIsoOfEq_inv_comp_d]
      have hi' := congrArg (fun z => z ≫ S.X₂.d p (p + 1) ≫ (σ (p + 1)).r) hi
      simp only [add_comp, Category.assoc, id_comp, S.f.comm_assoc, hr, comp_id] at hi'
      rw [eq_neg_add_iff_add_eq]
      simpa only [add_comm] using hi')
  have := mappingCone.quasiIso_descShortComplex hS
  apply (cancel_epi (_root_.DerivedCategory.Q.map (mappingCone.descShortComplex S))).1
  rw [_root_.DerivedCategory.descShortComplex_triangleOfSESδ, ← Category.assoc,
    ← Functor.map_comp, _root_.DerivedCategory.Q_map_eq_of_homotopy 𝒜 H]

/-- The image in the derived category of a degreewise split homotopy triangle
is distinguished. -/
@[stacks 0154]
theorem degreewiseSplitImage_distinguished
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    _root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ) ∈
      distTriang (_root_.DerivedCategory 𝒜) := sorry

/-- Lemma 13.12.3 (`0154`): the derived triangle of a degreewise split short
exact sequence is isomorphic to the image of its canonical homotopy triangle. -/
@[stacks 0154]
theorem triangle_isomorphic_degreewiseSplitImage
    {S : ShortComplex (CochainComplex 𝒜 ℤ)}
    (σ : ∀ n, (S.map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting) :
    IsIsomorphic
      (_root_.DerivedCategory.triangleOfSES
        (HomologicalComplex.shortExact_of_degreewise_shortExact S fun n =>
          (σ n).shortExact))
      (_root_.DerivedCategory.Qh.mapTriangle.obj
        (CochainComplex.trianglehOfDegreewiseSplit S σ)) := sorry

end CategoryTheory.DerivedCategory.ShortExact
