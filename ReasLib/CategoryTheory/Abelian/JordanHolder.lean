/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.Order.JordanHolder
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Abelian.FiniteLength
public import ReasLib.CategoryTheory.Subobject.Quotient

/-!
# Jordan-Hölder Theory for Abelian Categories

The subobject lattice of an object in an abelian category carries a canonical
`JordanHolderLattice` structure.  Covers are ordinary lattice covers and the factor attached to
`X ≤ Y` is the canonical subquotient `Y / X`.
-/

@[expose] public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Subobject

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- A comparable pair `X ≤ Y` is a cover exactly when the canonical subquotient `Y / X` is
simple. -/
theorem covBy_iff_simple_subobjectSubquotient {X Y : Subobject A} (hXY : X ≤ Y) :
    X ⋖ Y ↔ Simple (subobjectSubquotient hXY) := sorry

/-- The inclusion `X ⊓ Y ⊆ Y ⊆ X ⊔ Y` followed by the quotient map `X ⊔ Y ⟶ (X ⊔ Y) / X`
annihilates `X ⊓ Y`. -/
theorem subquotientSecondComparison_condition (X Y : Subobject A) :
    Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫
        (Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right ≫
          subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y)) = 0 := by
  rw [← Category.assoc, Subobject.ofLE_comp_ofLE,
    ← Subobject.ofLE_comp_ofLE (X ⊓ Y) X (X ⊔ Y) _root_.inf_le_left _root_.le_sup_left,
    Category.assoc, subobjectToSubquotient_comp_zero, Limits.comp_zero]

/-- The canonical comparison `Y / (X ⊓ Y) ⟶ (X ⊔ Y) / X` of the second isomorphism theorem,
induced by the inclusion `Y ⟶ X ⊔ Y` through the cokernel property of `Y ⟶ Y / (X ⊓ Y)`. -/
noncomputable def subquotientSecondComparison (X Y : Subobject A) :
    subobjectSubquotient (_root_.inf_le_right : X ⊓ Y ≤ Y) ⟶
      subobjectSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y) :=
  (subobjectToSubquotient_isCokernel (_root_.inf_le_right : X ⊓ Y ≤ Y)).desc
    (CokernelCofork.ofπ _ (subquotientSecondComparison_condition X Y))

/-- The second isomorphism comparison is characterized by the quotient maps out of `Y`. -/
@[reassoc (attr := simp)]
theorem subobjectToSubquotient_comp_subquotientSecondComparison (X Y : Subobject A) :
    subobjectToSubquotient (_root_.inf_le_right : X ⊓ Y ≤ Y) ≫
        subquotientSecondComparison X Y =
      Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right ≫
        subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y) :=
  (subobjectToSubquotient_isCokernel (_root_.inf_le_right : X ⊓ Y ≤ Y)).fac
    (CokernelCofork.ofπ _ (subquotientSecondComparison_condition X Y)) WalkingParallelPair.one

/-- The second isomorphism comparison is monic: quotienting `Y` by `X ⊓ Y` removes exactly
the kernel of its map to `(X ⊔ Y) / X`. -/
instance subquotientSecondComparison_mono (X Y : Subobject A) :
    Mono (subquotientSecondComparison X Y) := by
  let i := Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right
  let f := Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right ≫
    subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y)
  have hKernel : kernelSubobject f = Subobject.mk i := by
    apply le_antisymm
    · let k := (kernelSubobject f).arrow
      have hk : (k ≫ Y.arrow) ≫ cokernel.π X.arrow = 0 := by
        have hcomp : f ≫ (subobjectSubquotientSubobject
            (_root_.le_sup_left : X ≤ X ⊔ Y)).arrow = Y.arrow ≫ cokernel.π X.arrow := by
          dsimp [f]
          rw [Category.assoc, subobjectToSubquotient_comp_subobjectSubquotientInclusion,
            ← Category.assoc, Subobject.ofLE_arrow]
        calc
          (k ≫ Y.arrow) ≫ cokernel.π X.arrow =
              k ≫ (Y.arrow ≫ cokernel.π X.arrow) := Category.assoc _ _ _
          _ = k ≫ (f ≫ (subobjectSubquotientSubobject
              (_root_.le_sup_left : X ≤ X ⊔ Y)).arrow) := by rw [hcomp]
          _ = (k ≫ f) ≫ _ := (Category.assoc _ _ _).symm
          _ = 0 := by
            rw [show k ≫ f = 0 from kernelSubobject_arrow_comp f, zero_comp]
      let a := Abelian.monoLift X.arrow (k ≫ Y.arrow) hk
      have ha : a ≫ X.arrow = k ≫ Y.arrow := Abelian.monoLift_comp _ _ _
      refine Subobject.le_mk_of_comm ((Subobject.inf_isPullback X Y).lift a k ha) ?_
      exact (Subobject.inf_isPullback X Y).lift_snd a k ha
    · apply le_kernelSubobject
      rw [← Subobject.underlyingIso_hom_comp_eq_mk i, Category.assoc]
      change (Subobject.underlyingIso i).hom ≫
        (Subobject.ofLE (X ⊓ Y) Y _root_.inf_le_right ≫ _) = 0
      rw [subquotientSecondComparison_condition, comp_zero]
  let R₁ := ShortComplex.mk i
    (subobjectToSubquotient (_root_.inf_le_right : X ⊓ Y ≤ Y))
    (subobjectToSubquotient_comp_zero _)
  let R₂ := ShortComplex.mk i f (subquotientSecondComparison_condition X Y)
  have hR₂ : R₂.Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject i = kernelSubobject f
    rw [imageSubobject_mono, hKernel]
  let φ : R₁ ⟶ R₂ :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := subquotientSecondComparison X Y
      comm₁₂ := by simp [R₁, R₂]
      comm₂₃ := by
        dsimp [R₁, R₂, f]
        simp }
  exact ShortComplex.mono_of_epi_of_epi_of_mono φ hR₂
    inferInstance inferInstance inferInstance

/-- The second isomorphism comparison is epic: the images of `X` and `Y` generate `X ⊔ Y`,
and the quotient by `X` kills the image of `X`. -/
instance subquotientSecondComparison_epi (X Y : Subobject A) :
    Epi (subquotientSecondComparison X Y) := by
  have hEpi : Epi (Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right ≫
      subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y)) := by
    apply Preadditive.epi_of_cancel_zero
    intro T g hg
    let h := subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y) ≫ g
    have hX : Subobject.ofLE X (X ⊔ Y) _root_.le_sup_left ≫ h = 0 := by
      dsimp only [h]
      rw [← Category.assoc, subobjectToSubquotient_comp_zero, zero_comp]
    have hY : Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right ≫ h = 0 := by
      simpa [h, Category.assoc] using hg
    let K := Subobject.mk ((kernelSubobject h).arrow ≫ (X ⊔ Y).arrow)
    have hsup : X ⊔ Y ≤ K := by
      apply sup_le
      · apply Subobject.le_mk_of_comm
          (factorThruKernelSubobject h
            (Subobject.ofLE X (X ⊔ Y) _root_.le_sup_left) hX)
        rw [← Category.assoc, factorThruKernelSubobject_comp_arrow, Subobject.ofLE_arrow]
      · apply Subobject.le_mk_of_comm
          (factorThruKernelSubobject h
            (Subobject.ofLE Y (X ⊔ Y) _root_.le_sup_right) hY)
        rw [← Category.assoc, factorThruKernelSubobject_comp_arrow, Subobject.ofLE_arrow]
    have hid : Subobject.ofLEMk (X ⊔ Y)
        ((kernelSubobject h).arrow ≫ (X ⊔ Y).arrow) hsup ≫
          (kernelSubobject h).arrow = 𝟙 _ := by
      apply (cancel_mono (X ⊔ Y).arrow).1
      rw [Category.assoc, Subobject.ofLEMk_comp, Category.id_comp]
    have hh : h = 0 := by
      calc
        h = (Subobject.ofLEMk (X ⊔ Y)
            ((kernelSubobject h).arrow ≫ (X ⊔ Y).arrow) hsup ≫
              (kernelSubobject h).arrow) ≫ h := by rw [hid, Category.id_comp]
        _ = 0 := by rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]
    exact (cancel_epi
      (subobjectToSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y))).1 (by simpa using hh)
  exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hEpi
    (subobjectToSubquotient_comp_subquotientSecondComparison X Y)

/-- Second isomorphism theorem: the canonical comparison `Y / (X ⊓ Y) ⟶ (X ⊔ Y) / X` is an
isomorphism, with inverse supplied by the balanced construction for abelian categories. -/
instance subquotientSecondComparison_isIso (X Y : Subobject A) :
    IsIso (subquotientSecondComparison X Y) :=
  isIso_of_mono_of_epi (subquotientSecondComparison X Y)

/-- The second isomorphism theorem for canonical subquotients: `(X ⊔ Y) / X ≅ Y / (X ⊓ Y)`,
inverse to the canonical comparison induced by `Y ⟶ X ⊔ Y`. -/
noncomputable def subquotientSecondIso (X Y : Subobject A) :
    subobjectSubquotient (_root_.le_sup_left : X ≤ X ⊔ Y) ≅
      subobjectSubquotient (_root_.inf_le_right : X ⊓ Y ≤ Y) :=
  (asIso (subquotientSecondComparison X Y)).symm

/-- The inverse of the second isomorphism is the canonical comparison. -/
@[simp]
theorem subquotientSecondIso_inv (X Y : Subobject A) :
    (subquotientSecondIso X Y).inv = subquotientSecondComparison X Y := rfl

/-- The canonical Jordan-Hölder lattice structure on `Subobject A`, with factors represented by
canonical subquotients. -/
noncomputable instance instJordanHolderLattice : JordanHolderLattice (Subobject A) where
  IsMaximal := fun X Y ↦ X ⋖ Y
  lt_of_isMaximal := sorry
  sup_eq_of_isMaximal := sorry
  isMaximal_inf_left_of_isMaximal_sup := sorry
  Iso X Y := Nonempty
    (subobjectSubquotient (_root_.inf_le_right : X.1 ⊓ X.2 ≤ X.2) ≅
      subobjectSubquotient (_root_.inf_le_right : Y.1 ⊓ Y.2 ≤ Y.2))
  iso_symm := sorry
  iso_trans := sorry
  second_iso := sorry

/-- For comparable pairs, the Jordan-Hölder `Iso` relation is exactly isomorphism of the
corresponding canonical subquotients. -/
theorem iso_iff_nonempty_subobjectSubquotient_iso {X₁ X₂ Y₁ Y₂ : Subobject A}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) :
    JordanHolderLattice.Iso (X₁, X₂) (Y₁, Y₂) ↔
      Nonempty (subobjectSubquotient hX ≅ subobjectSubquotient hY) := sorry

end Subobject

end CategoryTheory

namespace CompositionSeries

open CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {A : C}

/-- The canonical subquotient attached to the `i`-th step of a composition series of
subobjects. -/
@[stacks 0FCK "composition-series factor object"]
noncomputable abbrev factor
    (s : CompositionSeries (Subobject A)) (i : Fin s.length) : C :=
  subobjectSubquotient (s.step i).le

/-- Every canonical factor of a composition series of subobjects is simple. -/
@[stacks 0FCK "simple composition-series factor"]
theorem factorSimple (s : CompositionSeries (Subobject A)) (i : Fin s.length) :
    Simple (s.factor i) := sorry

/-- Factorwise Jordan-Hölder for two composition series with the same endpoints. -/
theorem jordanHolderFactorsOfEndpoints
    (F G : CompositionSeries (Subobject A))
    (hhead : F.head = G.head) (hlast : F.last = G.last) :
    ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (F.factor i ≅ G.factor (σ i)) := sorry

/-- Lemma 12.9.7 (Tag 0FCK): two composition series from `0` to an object have isomorphic
factors up to a permutation. -/
@[stacks 0FCK]
theorem jordanHolderFactors
    (F G : CompositionSeries (Subobject A))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤)
    (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤) :
    ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (F.factor i ≅ G.factor (σ i)) := sorry

end CompositionSeries

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A finite-length object admits a composition series from the zero subobject to the whole
object. -/
theorem existsCompositionSeries (A : C) [IsFiniteLengthObject A] :
    ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := sorry

/-- Lemma 12.9.6 (Tag 0FCJ), in its canonical formulation: finite length is equivalent to the
existence of a composition series of subobjects from `0` to the whole object.  Combined with
`isFiniteLengthObject_iff`, this is the source statement in terms of Artinian and Noetherian
objects. -/
@[stacks 0FCJ]
theorem isFiniteLengthObject_iff_existsCompositionSeries (A : C) :
    IsFiniteLengthObject A ↔
      ∃ s : CompositionSeries (Subobject A), s.head = ⊥ ∧ s.last = ⊤ := sorry

end CategoryTheory
