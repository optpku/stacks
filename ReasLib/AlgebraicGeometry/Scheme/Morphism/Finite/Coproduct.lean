/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite morphisms from finite coproducts

A morphism induced from a finite coproduct is finite when every component morphism is finite.

@stack 0CYI
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A morphism from a finite coproduct is finite if every component morphism is finite. -/
@[stacks 0CYI]
theorem finite_sigma_desc {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [Finite ι] (hf : ∀ i, IsFinite (f i)) :
    IsFinite (Sigma.desc f) := by
  apply (Finite.induction_empty_option
    (P := fun ι : Type u => ∀ (X : ι → Scheme.{u}) (f : ∀ i, X i ⟶ Y),
      (∀ i, IsFinite (f i)) → IsFinite (Sigma.desc f))
    ?_ ?_ ?_ ι) X f hf
  · intro α β e IH X f hf
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      (Sigma.reindex e X).hom]
    convert IH (X ∘ e) (fun i ↦ f (e i)) (fun i ↦ hf (e i)) using 1
    ext i
    rw [← Category.assoc, Sigma.ι_reindex_hom]
    exact (Sigma.ι_desc f (e i)).trans (Sigma.ι_desc (fun i ↦ f (e i)) i).symm
  · intro X f hf
    have hinit : IsInitial (∐ X) :=
      IsInitial.ofUniqueHom
        (fun Z ↦ Sigma.desc (fun i ↦ PEmpty.elim i))
        (fun Z g ↦ by
          apply Sigma.hom_ext
          intro i
          exact PEmpty.elim i)
    let e := initialIsInitial.uniqueUpToIso hinit
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom]
    rw [initialIsInitial.hom_ext (e.hom ≫ Sigma.desc f) (initial.to Y)]
    infer_instance
  · intro α _ IH X f hf
    let tail : α → Scheme.{u} := fun i ↦ X (some i)
    let e : X none ⨿ (∐ tail) ≅ ∐ X :=
      { hom := coprod.desc (Sigma.ι X none) (Sigma.desc fun i ↦ Sigma.ι X (some i))
        inv := Sigma.desc fun o ↦ match o with
          | none => coprod.inl
          | some i => Sigma.ι tail i ≫ coprod.inr
        hom_inv_id := by
          apply coprod.hom_ext
          · rw [coprod.inl_desc_assoc, Sigma.ι_desc, Category.comp_id]
          · apply Sigma.hom_ext
            intro i
            rw [coprod.inr_desc_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc, Category.comp_id]
        inv_hom_id := by
          apply Sigma.hom_ext
          intro o
          cases o with
          | none => rw [Sigma.ι_desc_assoc, coprod.inl_desc, Category.comp_id]
          | some i =>
            rw [Sigma.ι_desc_assoc, Category.assoc, coprod.inr_desc, Sigma.ι_desc,
              Category.comp_id] }
    -- Local instance justification (proof-local temporary data): register the finite head component.
    letI : IsFinite (f none) := hf none
    -- Local instance justification (proof-local temporary data): register the finite tail coproduct.
    letI : IsFinite (Sigma.desc fun i : α ↦ f (some i)) :=
      IH tail (fun i ↦ f (some i)) (fun i ↦ hf (some i))
    -- Local instance justification (proof-local temporary data): register the decomposition isomorphism.
    letI := e.isIso_hom
    rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite) e.hom]
    change IsFinite
      (coprod.desc (Sigma.ι X none) (Sigma.desc fun i ↦ Sigma.ι X (some i)) ≫ Sigma.desc f)
    convert (inferInstance : IsFinite
      (coprod.desc (f none) (Sigma.desc fun i : α ↦ f (some i)))) using 1
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, coprod.inl_desc, Sigma.ι_desc]
    · apply Sigma.hom_ext
      intro i
      calc
        Sigma.ι tail i ≫ coprod.inr ≫
              (coprod.desc (Sigma.ι X none) (Sigma.desc fun i ↦ Sigma.ι X (some i)) ≫
                Sigma.desc f) = f (some i) := by
          rw [coprod.inr_desc_assoc, Sigma.ι_desc_assoc, Sigma.ι_desc]
        _ = Sigma.ι tail i ≫ coprod.inr ≫
              coprod.desc (f none) (Sigma.desc fun i : α ↦ f (some i)) := by
          symm
          rw [coprod.inr_desc, Sigma.ι_desc]

/-- The morphism from a finite coproduct induced by a family of finite morphisms is finite. -/
instance instIsFiniteSigmaDesc {ι : Type u} {X : ι → Scheme.{u}} {Y : Scheme.{u}}
    (f : ∀ i, X i ⟶ Y) [Finite ι] [∀ i, IsFinite (f i)] :
    IsFinite (Sigma.desc f) :=
  finite_sigma_desc f (fun i ↦ show IsFinite (f i) from inferInstance)

end AlgebraicGeometry
