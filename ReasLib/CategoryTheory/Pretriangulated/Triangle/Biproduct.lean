/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Binary Biproducts of Triangles

Mathlib's binaryBiproductTriangle is the split triangle attached to two
objects. This leaf instead constructs the objectwise binary biproduct of two
arbitrary triangles.
-/

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.Pretriangulated

section Basic

variable {D : Type u} [Category.{v} D] [HasZeroMorphisms D] [HasShift D ℤ]
  [HasBinaryBiproducts D]

/-- Stacks 05QS, Lemma 13.4.10: the objectwise binary biproduct of two triangles. -/
@[stacks 05QS, simps!]
def biproductTriangle (T₁ T₂ : Triangle D) : Triangle D :=
  Triangle.mk
    (biprod.map T₁.mor₁ T₂.mor₁)
    (biprod.map T₁.mor₂ T₂.mor₂)
    (biprod.map T₁.mor₃ T₂.mor₃ ≫
      Functor.biprodComparison' (shiftFunctor D (1 : ℤ)) T₁.obj₁ T₂.obj₁)

/-- The first square for the left inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inl_comm₁ (T₁ T₂ : Triangle D) :
    T₁.mor₁ ≫ biprod.inl = biprod.inl ≫ (biproductTriangle T₁ T₂).mor₁ := sorry

/-- The second square for the left inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inl_comm₂ (T₁ T₂ : Triangle D) :
    T₁.mor₂ ≫ biprod.inl = biprod.inl ≫ (biproductTriangle T₁ T₂).mor₂ := sorry

/-- The third square for the left inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inl_comm₃ (T₁ T₂ : Triangle D) :
    T₁.mor₃ ≫ (biprod.inl)⟦(1 : ℤ)⟧' = biprod.inl ≫ (biproductTriangle T₁ T₂).mor₃ := sorry

/-- The canonical left inclusion into an objectwise binary biproduct triangle. -/
@[simps!]
def biproductTriangle.inl (T₁ T₂ : Triangle D) : T₁ ⟶ biproductTriangle T₁ T₂ :=
  Triangle.homMk _ _ biprod.inl biprod.inl biprod.inl
    (biproductTriangle.inl_comm₁ T₁ T₂)
    (biproductTriangle.inl_comm₂ T₁ T₂)
    (biproductTriangle.inl_comm₃ T₁ T₂)

/-- The first square for the right inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inr_comm₁ (T₁ T₂ : Triangle D) :
    T₂.mor₁ ≫ biprod.inr = biprod.inr ≫ (biproductTriangle T₁ T₂).mor₁ := sorry

/-- The second square for the right inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inr_comm₂ (T₁ T₂ : Triangle D) :
    T₂.mor₂ ≫ biprod.inr = biprod.inr ≫ (biproductTriangle T₁ T₂).mor₂ := sorry

/-- The third square for the right inclusion into the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.inr_comm₃ (T₁ T₂ : Triangle D) :
    T₂.mor₃ ≫ (biprod.inr)⟦(1 : ℤ)⟧' = biprod.inr ≫ (biproductTriangle T₁ T₂).mor₃ := sorry

/-- The canonical right inclusion into an objectwise binary biproduct triangle. -/
@[simps!]
def biproductTriangle.inr (T₁ T₂ : Triangle D) : T₂ ⟶ biproductTriangle T₁ T₂ :=
  Triangle.homMk _ _ biprod.inr biprod.inr biprod.inr
    (biproductTriangle.inr_comm₁ T₁ T₂)
    (biproductTriangle.inr_comm₂ T₁ T₂)
    (biproductTriangle.inr_comm₃ T₁ T₂)

/-- The first square for the left projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.fst_comm₁ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₁ ≫ biprod.fst = biprod.fst ≫ T₁.mor₁ := sorry

/-- The second square for the left projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.fst_comm₂ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₂ ≫ biprod.fst = biprod.fst ≫ T₁.mor₂ := sorry

/-- The third square for the left projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.fst_comm₃ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₃ ≫ (biprod.fst)⟦(1 : ℤ)⟧' = biprod.fst ≫ T₁.mor₃ := sorry

/-- The canonical left projection from an objectwise binary biproduct triangle. -/
@[simps!]
def biproductTriangle.fst (T₁ T₂ : Triangle D) : biproductTriangle T₁ T₂ ⟶ T₁ :=
  Triangle.homMk _ _ biprod.fst biprod.fst biprod.fst
    (biproductTriangle.fst_comm₁ T₁ T₂)
    (biproductTriangle.fst_comm₂ T₁ T₂)
    (biproductTriangle.fst_comm₃ T₁ T₂)

/-- The first square for the right projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.snd_comm₁ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₁ ≫ biprod.snd = biprod.snd ≫ T₂.mor₁ := sorry

/-- The second square for the right projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.snd_comm₂ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₂ ≫ biprod.snd = biprod.snd ≫ T₂.mor₂ := sorry

/-- The third square for the right projection from the objectwise binary biproduct. -/
@[reassoc]
theorem biproductTriangle.snd_comm₃ (T₁ T₂ : Triangle D) :
    (biproductTriangle T₁ T₂).mor₃ ≫ (biprod.snd)⟦(1 : ℤ)⟧' = biprod.snd ≫ T₂.mor₃ := sorry

/-- The canonical right projection from an objectwise binary biproduct triangle. -/
@[simps!]
def biproductTriangle.snd (T₁ T₂ : Triangle D) : biproductTriangle T₁ T₂ ⟶ T₂ :=
  Triangle.homMk _ _ biprod.snd biprod.snd biprod.snd
    (biproductTriangle.snd_comm₁ T₁ T₂)
    (biproductTriangle.snd_comm₂ T₁ T₂)
    (biproductTriangle.snd_comm₃ T₁ T₂)

/-- The first square for a lift into an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.lift_comm₁ {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) :
    S.mor₁ ≫ biprod.lift φ₁.hom₂ φ₂.hom₂ =
      biprod.lift φ₁.hom₁ φ₂.hom₁ ≫ (biproductTriangle T₁ T₂).mor₁ := sorry

/-- The second square for a lift into an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.lift_comm₂ {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) :
    S.mor₂ ≫ biprod.lift φ₁.hom₃ φ₂.hom₃ =
      biprod.lift φ₁.hom₂ φ₂.hom₂ ≫ (biproductTriangle T₁ T₂).mor₂ := sorry

/-- The third square for a lift into an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.lift_comm₃ {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) :
    S.mor₃ ≫ (biprod.lift φ₁.hom₁ φ₂.hom₁)⟦(1 : ℤ)⟧' =
      biprod.lift φ₁.hom₃ φ₂.hom₃ ≫ (biproductTriangle T₁ T₂).mor₃ := sorry

/-- The lift of two triangle morphisms with common source. -/
@[simps!]
def biproductTriangle.lift {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) : S ⟶ biproductTriangle T₁ T₂ :=
  Triangle.homMk _ _
    (biprod.lift φ₁.hom₁ φ₂.hom₁)
    (biprod.lift φ₁.hom₂ φ₂.hom₂)
    (biprod.lift φ₁.hom₃ φ₂.hom₃)
    (biproductTriangle.lift_comm₁ φ₁ φ₂)
    (biproductTriangle.lift_comm₂ φ₁ φ₂)
    (biproductTriangle.lift_comm₃ φ₁ φ₂)

/-- The first square for a descent from an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.desc_comm₁ {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) :
    (biproductTriangle T₁ T₂).mor₁ ≫ biprod.desc φ₁.hom₂ φ₂.hom₂ =
      biprod.desc φ₁.hom₁ φ₂.hom₁ ≫ S.mor₁ := sorry

/-- The second square for a descent from an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.desc_comm₂ {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) :
    (biproductTriangle T₁ T₂).mor₂ ≫ biprod.desc φ₁.hom₃ φ₂.hom₃ =
      biprod.desc φ₁.hom₂ φ₂.hom₂ ≫ S.mor₂ := sorry

/-- The third square for a descent from an objectwise binary biproduct triangle. -/
@[reassoc]
theorem biproductTriangle.desc_comm₃ {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) :
    (biproductTriangle T₁ T₂).mor₃ ≫
        (biprod.desc φ₁.hom₁ φ₂.hom₁)⟦(1 : ℤ)⟧' =
      biprod.desc φ₁.hom₃ φ₂.hom₃ ≫ S.mor₃ := sorry

/-- The descent of two triangle morphisms with common target. -/
@[simps!]
def biproductTriangle.desc {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) : biproductTriangle T₁ T₂ ⟶ S :=
  Triangle.homMk _ _
    (biprod.desc φ₁.hom₁ φ₂.hom₁)
    (biprod.desc φ₁.hom₂ φ₂.hom₂)
    (biprod.desc φ₁.hom₃ φ₂.hom₃)
    (biproductTriangle.desc_comm₁ φ₁ φ₂)
    (biproductTriangle.desc_comm₂ φ₁ φ₂)
    (biproductTriangle.desc_comm₃ φ₁ φ₂)

/-- A lift followed by the left projection recovers its left input. -/
@[simp]
theorem biproductTriangle.lift_fst {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) :
    biproductTriangle.lift φ₁ φ₂ ≫ biproductTriangle.fst T₁ T₂ = φ₁ := sorry

/-- A lift followed by the right projection recovers its right input. -/
@[simp]
theorem biproductTriangle.lift_snd {S T₁ T₂ : Triangle D}
    (φ₁ : S ⟶ T₁) (φ₂ : S ⟶ T₂) :
    biproductTriangle.lift φ₁ φ₂ ≫ biproductTriangle.snd T₁ T₂ = φ₂ := sorry

/-- The left inclusion followed by a descent recovers the left input. -/
@[simp]
theorem biproductTriangle.inl_desc {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) :
    biproductTriangle.inl T₁ T₂ ≫ biproductTriangle.desc φ₁ φ₂ = φ₁ := sorry

/-- The right inclusion followed by a descent recovers the right input. -/
@[simp]
theorem biproductTriangle.inr_desc {T₁ T₂ S : Triangle D}
    (φ₁ : T₁ ⟶ S) (φ₂ : T₂ ⟶ S) :
    biproductTriangle.inr T₁ T₂ ≫ biproductTriangle.desc φ₁ φ₂ = φ₂ := sorry

/-- Morphisms into an objectwise binary biproduct triangle are determined by their projections. -/
@[ext]
theorem biproductTriangle.hom_ext {T₁ T₂ S : Triangle D}
    (f g : S ⟶ biproductTriangle T₁ T₂)
    (h₁ : f ≫ biproductTriangle.fst T₁ T₂ = g ≫ biproductTriangle.fst T₁ T₂)
    (h₂ : f ≫ biproductTriangle.snd T₁ T₂ = g ≫ biproductTriangle.snd T₁ T₂) :
    f = g := sorry

/-- Morphisms out of an objectwise binary biproduct triangle are determined by their inclusions. -/
@[ext]
theorem biproductTriangle.hom_ext' {T₁ T₂ S : Triangle D}
    (f g : biproductTriangle T₁ T₂ ⟶ S)
    (h₁ : biproductTriangle.inl T₁ T₂ ≫ f = biproductTriangle.inl T₁ T₂ ≫ g)
    (h₂ : biproductTriangle.inr T₁ T₂ ≫ f = biproductTriangle.inr T₁ T₂ ≫ g) :
    f = g := sorry

end Basic

section Bicone

variable {D : Type u} [Category.{v} D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [HasBinaryBiproducts D]

/-- The left inclusion followed by the left projection is the identity. -/
@[simp]
theorem biproductTriangle.inl_fst (T₁ T₂ : Triangle D) :
    biproductTriangle.inl T₁ T₂ ≫ biproductTriangle.fst T₁ T₂ = 𝟙 T₁ := sorry

/-- The left inclusion followed by the right projection is zero. -/
@[simp]
theorem biproductTriangle.inl_snd (T₁ T₂ : Triangle D) :
    biproductTriangle.inl T₁ T₂ ≫ biproductTriangle.snd T₁ T₂ = 0 := sorry

/-- The right inclusion followed by the left projection is zero. -/
@[simp]
theorem biproductTriangle.inr_fst (T₁ T₂ : Triangle D) :
    biproductTriangle.inr T₁ T₂ ≫ biproductTriangle.fst T₁ T₂ = 0 := sorry

/-- The right inclusion followed by the right projection is the identity. -/
@[simp]
theorem biproductTriangle.inr_snd (T₁ T₂ : Triangle D) :
    biproductTriangle.inr T₁ T₂ ≫ biproductTriangle.snd T₁ T₂ = 𝟙 T₂ := sorry

/-- The binary bicone of triangles with vertex biproductTriangle T₁ T₂. -/
@[stacks 05QS]
def biproductTriangle.bicone (T₁ T₂ : Triangle D) : BinaryBicone T₁ T₂ where
  pt := biproductTriangle T₁ T₂
  fst := biproductTriangle.fst T₁ T₂
  snd := biproductTriangle.snd T₁ T₂
  inl := biproductTriangle.inl T₁ T₂
  inr := biproductTriangle.inr T₁ T₂
  inl_fst := biproductTriangle.inl_fst T₁ T₂
  inl_snd := biproductTriangle.inl_snd T₁ T₂
  inr_fst := biproductTriangle.inr_fst T₁ T₂
  inr_snd := biproductTriangle.inr_snd T₁ T₂

/-- The displayed binary bicone is a biproduct in the category of triangles. -/
@[stacks 05QS]
def biproductTriangle.isBilimit (T₁ T₂ : Triangle D) :
    (biproductTriangle.bicone T₁ T₂).IsBilimit where
  isLimit :=
    BinaryFan.IsLimit.mk _
      (fun f g ↦ biproductTriangle.lift f g)
      (fun f g ↦ biproductTriangle.lift_fst f g)
      (fun f g ↦ biproductTriangle.lift_snd f g)
      (fun f g m hm₁ hm₂ ↦ sorry)
  isColimit :=
    BinaryCofan.IsColimit.mk _
      (fun f g ↦ biproductTriangle.desc f g)
      (fun f g ↦ biproductTriangle.inl_desc f g)
      (fun f g ↦ biproductTriangle.inr_desc f g)
      (fun f g m hm₁ hm₂ ↦ sorry)

end Bicone

section Distinguished

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [HasBinaryBiproducts D] [Pretriangulated D]

/-- Stacks 05QS: the objectwise binary biproduct of distinguished triangles is distinguished. -/
@[stacks 05QS]
theorem biproductTriangle.distinguished {T₁ T₂ : Triangle D}
    (h₁ : T₁ ∈ distTriang D) (h₂ : T₂ ∈ distTriang D) :
    biproductTriangle T₁ T₂ ∈ distTriang D := sorry

/-- Stacks 05QS: a distinguished objectwise binary biproduct has a distinguished left summand. -/
@[stacks 05QS]
theorem biproductTriangle.distinguished_left {T₁ T₂ : Triangle D}
    (h : biproductTriangle T₁ T₂ ∈ distTriang D) :
    T₁ ∈ distTriang D := sorry

/-- Stacks 05QS: a distinguished objectwise binary biproduct has a distinguished right summand. -/
@[stacks 05QS]
theorem biproductTriangle.distinguished_right {T₁ T₂ : Triangle D}
    (h : biproductTriangle T₁ T₂ ∈ distTriang D) :
    T₂ ∈ distTriang D := sorry

/-- Stacks 05QS, Lemma 13.4.10: an objectwise binary biproduct triangle is distinguished iff both summands are. -/
@[stacks 05QS]
theorem biproductTriangle.distinguished_iff {T₁ T₂ : Triangle D} :
    biproductTriangle T₁ T₂ ∈ distTriang D ↔
      T₁ ∈ distTriang D ∧ T₂ ∈ distTriang D := sorry

end Distinguished

end CategoryTheory.Pretriangulated
