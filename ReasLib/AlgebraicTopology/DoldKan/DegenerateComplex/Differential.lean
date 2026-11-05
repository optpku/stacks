/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateSubobject
public import Mathlib.AlgebraicTopology.DoldKan.Degeneracies
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degreewise degenerate complexes

This leaf owns the alternating-face differential restricted to degreewise degenerate subobjects,
the resulting chain complex, and its canonical inclusion.

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

namespace degenerateComplex

omit [HasZeroObject C] in
set_option backward.isDefEq.respectTransparency false in
private theorem image_ι_comp_eq_zero_of_comp_eq_zero {X Y Z : C}
    (morphism : X ⟶ Y) (next : Y ⟶ Z) (vanishes : morphism ≫ next = 0) :
    image.ι morphism ≫ next = 0 := by
  letI : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  let paired : X ⟶ Y ⊞ Z := biprod.lift morphism 0
  let graph : Y ⟶ Y ⊞ Z := biprod.lift (𝟙 Y) next
  haveI : Mono graph := by
    constructor
    intro source first second equality
    have projected := congrArg (fun arrow => arrow ≫ (biprod.fst : Y ⊞ Z ⟶ Y)) equality
    simpa only [graph, Category.assoc, biprod.lift_fst, Category.comp_id] using projected
  let leftFactor : MonoFactorisation paired :=
    { I := Y
      m := biprod.inl
      e := morphism
      fac := by ext <;> simp [paired] }
  let graphFactor : MonoFactorisation paired :=
    { I := Y
      m := graph
      e := morphism
      fac := by ext <;> simp [paired, graph, vanishes] }
  let first : image paired ⟶ Y := image.lift leftFactor
  let second : image paired ⟶ Y := image.lift graphFactor
  have first_eq_second : first = second := by
    have equality := (image.lift_fac leftFactor).trans (image.lift_fac graphFactor).symm
    have projected := congrArg (fun arrow => arrow ≫ (biprod.fst : Y ⊞ Z ⟶ Y)) equality
    simpa only [leftFactor, graphFactor, graph, Category.assoc, biprod.inl_fst,
      biprod.lift_fst, Category.comp_id] using projected
  have annihilates : first ≫ next = 0 := by
    have equality := (image.lift_fac graphFactor).trans (image.lift_fac leftFactor).symm
    have projected := congrArg (fun arrow => arrow ≫ (biprod.snd : Y ⊞ Z ⟶ Z)) equality
    have second_annihilates : second ≫ next = 0 := by
      simpa only [leftFactor, graphFactor, graph, Category.assoc, biprod.inl_snd,
        biprod.lift_snd, comp_zero] using projected
    rw [first_eq_second]
    exact second_annihilates
  have first_fac : first ≫ (biprod.inl : Y ⟶ Y ⊞ Z) = image.ι paired :=
    image.lift_fac leftFactor
  haveI : Mono first := by
    constructor
    intro source firstMap secondMap equality
    apply (cancel_mono (image.ι paired)).1
    rw [← first_fac, ← Category.assoc, ← Category.assoc, equality]
  let originalFactor : MonoFactorisation morphism :=
    { I := image paired
      m := first
      e := factorThruImage paired
      fac := image.fac_lift leftFactor }
  calc
    image.ι morphism ≫ next = image.lift originalFactor ≫ first ≫ next := by
      rw [← image.lift_fac originalFactor, Category.assoc]
    _ = 0 := by rw [annihilates, comp_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The complementary Dold--Kan projector acts as the identity on degenerate simplices. -/
@[reassoc]
theorem arrow_comp_QInfty (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).arrow ≫ (QInfty : K[U] ⟶ K[U]).f n =
      (degenerateSubobject U n).arrow := by
  have inclusion : degenerateSubobject U n ≤
      imageSubobject ((QInfty : K[U] ⟶ K[U]).f n) := by
    cases n with
    | zero => exact bot_le
    | succ degree =>
      change Finset.univ.sup (fun index : Fin (degree + 1) ↦ imageSubobject (U.σ index)) ≤ _
      apply Finset.sup_le
      intro index membership
      apply imageSubobject_le (U.σ index)
        (U.σ index ≫ factorThruImageSubobject ((QInfty : K[U] ⟶ K[U]).f (degree + 1)))
      simp only [Category.assoc, imageSubobject_arrow_comp, QInfty,
        HomologicalComplex.sub_f_apply, HomologicalComplex.id_f, Preadditive.comp_sub,
        σ_comp_PInfty, sub_zero]
      exact Category.comp_id _
  have image_annihilates_P :
      (imageSubobject ((QInfty : K[U] ⟶ K[U]).f n)).arrow ≫ PInfty.f n = 0 := by
    rw [← imageSubobject_arrow, Category.assoc,
      image_ι_comp_eq_zero_of_comp_eq_zero _ _ (QInfty_f_comp_PInfty_f n), comp_zero]
  have degenerate_annihilates_P : (degenerateSubobject U n).arrow ≫ PInfty.f n = 0 := by
    rw [← ofLE_arrow inclusion, Category.assoc, image_annihilates_P, comp_zero]
  simp only [QInfty, HomologicalComplex.sub_f_apply, HomologicalComplex.id_f,
    Preadditive.comp_sub, degenerate_annihilates_P, sub_zero]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- The projector `Q∞` factors through the degree-`n` degenerate subobject. -/
@[stacks 019A "degenerate projection component factorization"]
theorem π.app.factors (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors ((QInfty : K[U] ⟶ K[U]).f n) := by
  classical
  cases n with
  | zero =>
    rw [QInfty_f_0]
    exact factors_zero
  | succ n =>
    rw [QInfty_f, decomposition_Q]
    apply (factors_iff _ _).2
    refine ⟨∑ index : Fin (n + 1) with index.val < n + 1,
      (P index.val).f (n + 1) ≫ U.δ index.rev.succ ≫
        factorThruImageSubobject (U.σ index.rev) ≫
          ofLE _ _ (by
            change imageSubobject (U.σ index.rev) ≤
              Finset.univ.sup (fun degeneracy : Fin (n + 1) ↦ imageSubobject (U.σ degeneracy))
            exact Finset.le_sup (f := fun degeneracy : Fin (n + 1) ↦
              imageSubobject (U.σ degeneracy)) (Finset.mem_univ index.rev)), ?_⟩
    change _ ≫ (degenerateSubobject U (n + 1)).arrow = _
    simp only [Preadditive.sum_comp, Category.assoc, ofLE_arrow,
      imageSubobject_arrow_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The alternating-face differential maps the degree-`n + 1` degenerate subobject into the
degree-`n` degenerate subobject. -/
@[stacks 019A "degenerate differential factorization"]
theorem d.factors (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U n).Factors
      ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n) := by
  apply (factors_iff _ _).2
  refine ⟨(degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n ≫
    (degenerateSubobject U n).factorThru ((QInfty : K[U] ⟶ K[U]).f n)
      (π.app.factors U n), ?_⟩
  change _ ≫ (degenerateSubobject U n).arrow = _
  simp only [Category.assoc, factorThru_arrow]
  rw [← (QInfty : K[U] ⟶ K[U]).comm (n + 1) n, ← Category.assoc, arrow_comp_QInfty]

/-- The differential induced on the degreewise degenerate subobjects. -/
@[stacks 019A "degenerate differential"]
def d (U : SimplicialObject C) (n : ℕ) :
    (degenerateSubobject U (n + 1) : C) ⟶ (degenerateSubobject U n : C) :=
  (degenerateSubobject U n).factorThru
    ((degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n)
    (d.factors U n)

/-- The induced degenerate differential agrees after inclusion with the alternating-face
differential. -/
@[reassoc, stacks 019A "degenerate differential inclusion formula"]
theorem d.arrow (U : SimplicialObject C) (n : ℕ) :
    d U n ≫ (degenerateSubobject U n).arrow =
      (degenerateSubobject U (n + 1)).arrow ≫ (K[U]).d (n + 1) n := factorThru_arrow _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- Consecutive induced degenerate differentials compose to zero. -/
@[stacks 019A "degenerate differential squares to zero"]
theorem d.squared (U : SimplicialObject C) (n : ℕ) :
    d U (n + 1) ≫ d U n = 0 := by
  apply (cancel_mono (degenerateSubobject U n).arrow).1
  simp only [Category.assoc, d.arrow, d.arrow_assoc, HomologicalComplex.d_comp_d,
    comp_zero, zero_comp]

end degenerateComplex

/-- The degenerate subcomplex `D(U)` of the alternating-face complex of a simplicial object. -/
@[stacks 019A "degenerate subcomplex"]
def degenerateComplex (U : SimplicialObject C) : ChainComplex C ℕ :=
  ChainComplex.of (fun n ↦ (degenerateSubobject U n : C))
    (degenerateComplex.d U) (degenerateComplex.d.squared U)

@[inherit_doc]
scoped[DoldKan] notation "D[" X "]" => AlgebraicTopology.DoldKan.degenerateComplex X

namespace degenerateComplex

/-- The degree-`n` object of the degenerate complex is the degreewise degenerate subobject. -/
@[simp, stacks 019A "degenerate complex object formula"]
theorem obj_X (U : SimplicialObject C) (n : ℕ) :
    D[U].X n = (degenerateSubobject U n : C) := rfl

/-- The adjacent differential of the degenerate complex is the induced degenerate differential. -/
@[stacks 019A "degenerate complex differential formula"]
theorem obj_d (U : SimplicialObject C) (n : ℕ) :
    D[U].d (n + 1) n = d U n :=
  ChainComplex.of_d (fun degree ↦ (degenerateSubobject U degree : C)) (d U) n

/-- The degreewise subobject inclusions commute with every relevant differential. -/
@[stacks 019A "degenerate inclusion commutes with differentials"]
theorem ι.comm (U : SimplicialObject C) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    (degenerateSubobject U i).arrow ≫ (K[U]).d i j =
      (D[U]).d i j ≫ (degenerateSubobject U j).arrow := by
  change j + 1 = i at hij
  subst i
  rw [obj_d]
  exact (d.arrow U j).symm

/-- The inclusion of `D(U)` into the alternating-face complex `K(U)`. -/
@[stacks 019A "degenerate subcomplex inclusion"]
def ι (U : SimplicialObject C) : D[U] ⟶ K[U] where
  f n := (degenerateSubobject U n).arrow
  comm' := ι.comm U

/-- The degree-`n` component of the inclusion of the degenerate complex is the subobject arrow. -/
@[simp, stacks 019A "degenerate inclusion component"]
theorem ι.f (U : SimplicialObject C) (n : ℕ) :
    (ι U).f n = (degenerateSubobject U n).arrow := rfl

end degenerateComplex

end AlgebraicTopology.DoldKan
