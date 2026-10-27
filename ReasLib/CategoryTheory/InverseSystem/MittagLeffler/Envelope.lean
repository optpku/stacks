/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.ObjectProperty.Cover

/-!
# Mittag-Leffler Envelopes

Finite prefix products turn any sequential inverse system into a Mittag-Leffler system with a
monomorphic comparison map.  This leaf owns the concrete prefix-product tower, its comparison
morphism, and the resulting object-property interface.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

namespace FiniteProductEnvelope

section FiniteProducts

variable [HasFiniteProducts A]

/-- The product of the first `n + 1` stages of a sequential inverse system. -/
noncomputable abbrev obj (F : SequentialInverseSystem A) (n : ℕ) : A :=
  ∏ᶜ fun i : Fin (n + 1) ↦ F.obj (op (i : ℕ))

/-- The projection which drops the final coordinate of consecutive prefix products. -/
noncomputable def drop (F : SequentialInverseSystem A) (n : ℕ) :
    obj F (n + 1) ⟶ obj F n :=
  Pi.lift fun i ↦
    Pi.π (fun j : Fin (n + 2) ↦ F.obj (op (j : ℕ))) i.castSucc

/-- The sequential inverse system of finite prefix products. -/
noncomputable def tower (F : SequentialInverseSystem A) : SequentialInverseSystem A :=
  Functor.ofOpSequence (drop F)

/-- The successor transition of the prefix-product tower is its coordinate-dropping map. -/
theorem tower_step (F : SequentialInverseSystem A) (n : ℕ) :
    (tower F).stepMap n = drop F n := by
  exact Functor.ofOpSequence_map_homOfLE_succ (drop F) n

/-- The map from the `n`th stage of a system into its finite prefix product. -/
noncomputable def ιApp (F : SequentialInverseSystem A) (n : ℕ) :
    F.obj (op n) ⟶ obj F n :=
  Pi.lift fun i ↦ F.transitionMap (Nat.le_of_lt_succ i.isLt)

set_option backward.isDefEq.respectTransparency false in
/-- The naturality identity for the finite-prefix comparison maps. -/
theorem ιApp_naturality (F : SequentialInverseSystem A) (n : ℕ) :
    F.map (homOfLE (Nat.le_add_right n 1)).op ≫ ιApp F n =
      ιApp F (n + 1) ≫ (tower F).map (homOfLE (Nat.le_add_right n 1)).op := by
  change F.stepMap n ≫ ιApp F n = ιApp F (n + 1) ≫ (tower F).stepMap n
  rw [tower_step]
  apply Pi.hom_ext
  intro i
  simp only [ιApp, drop, Category.assoc, Pi.lift_π]
  rw [← F.map_comp]
  rfl

/-- The comparison from a sequential inverse system to its finite prefix-product tower. -/
noncomputable def ι (F : SequentialInverseSystem A) : F ⟶ tower F :=
  NatTrans.ofOpSequence (fun n ↦ ιApp F n) (fun n ↦ ιApp_naturality F n)

/-- The `n`th component of the finite-prefix comparison is the corresponding product lift. -/
theorem ι_app (F : SequentialInverseSystem A) (n : ℕ) :
    (ι F).app (op n) = ιApp F n := by
  rfl

/-- Projection to the final factor of a finite prefix product. -/
noncomputable def retraction (F : SequentialInverseSystem A) (n : ℕ) :
    obj F n ⟶ F.obj (op n) :=
  Pi.π (fun i : Fin (n + 1) ↦ F.obj (op (i : ℕ))) (Fin.last n)

set_option backward.isDefEq.respectTransparency false in
/-- The finite-prefix comparison at a stage is split by its final-coordinate projection. -/
theorem ιApp_comp_retraction (F : SequentialInverseSystem A) (n : ℕ) :
    ιApp F n ≫ retraction F n = 𝟙 _ := by
  simp only [ιApp, retraction, Pi.lift_π]
  change F.map (𝟙 (op n)) = 𝟙 _
  exact F.map_id (op n)

/-- Each component of the finite-prefix comparison is a split monomorphism. -/
instance ιApp_isSplitMono (F : SequentialInverseSystem A) (n : ℕ) :
    IsSplitMono (ιApp F n) := by
  exact IsSplitMono.mk' ⟨retraction F n, ιApp_comp_retraction F n⟩

/-- The finite-prefix comparison is monomorphic. -/
instance ι_mono (F : SequentialInverseSystem A) : Mono (ι F) := by
  haveI (n : ℕᵒᵖ) : Mono ((ι F).app n) := by
    change Mono (ιApp F n.unop)
    infer_instance
  exact NatTrans.mono_of_mono_app (ι F)

end FiniteProducts

section ZeroMorphisms

variable [HasFiniteProducts A] [HasZeroMorphisms A]

/-- The extension of a finite prefix product by a zero final coordinate. -/
noncomputable def zeroExtension (F : SequentialInverseSystem A) (n : ℕ) :
    obj F n ⟶ obj F (n + 1) :=
  Pi.lift fun i ↦
    Fin.lastCases
      (0 : obj F n ⟶ F.obj (op (n + 1)))
      (fun j ↦ Pi.π (fun k : Fin (n + 1) ↦ F.obj (op (k : ℕ))) j)
      i

set_option backward.isDefEq.respectTransparency false in
/-- Extending by zero is a section of the coordinate-dropping map. -/
theorem zeroExtension_comp_drop (F : SequentialInverseSystem A) (n : ℕ) :
    zeroExtension F n ≫ drop F n = 𝟙 _ := by
  apply Pi.hom_ext
  intro i
  simp [zeroExtension, drop, Category.assoc]

end ZeroMorphisms

/-- Every transition in the finite prefix-product tower is a split epimorphism. -/
instance drop_isSplitEpi [HasFiniteProducts A] [HasZeroMorphisms A]
    (F : SequentialInverseSystem A) (n : ℕ) :
    IsSplitEpi (drop F n) := by
  exact IsSplitEpi.mk' ⟨zeroExtension F n, zeroExtension_comp_drop F n⟩

section MittagLeffler

variable [HasFiniteProducts A] [HasZeroMorphisms A] [HasImages A]

set_option backward.isDefEq.respectTransparency false in
/-- The finite prefix-product tower satisfies the Mittag-Leffler condition. -/
theorem isMittagLeffler (F : SequentialInverseSystem A) :
    (tower F).IsMittagLeffler := by
  have hsplit : ∀ {i k : ℕ} (hik : i ≤ k),
      IsSplitEpi ((tower F).transitionMap hik) := by
    intro i k hik
    induction k, hik using Nat.le_induction with
    | base =>
        change IsSplitEpi ((tower F).map (𝟙 (op i)))
        rw [Functor.map_id]
        infer_instance
    | succ k hik ih =>
        have hmap : (tower F).transitionMap (Nat.le_succ_of_le hik) =
            (tower F).stepMap k ≫ (tower F).transitionMap hik :=
          (tower F).map_comp (homOfLE (Nat.le_succ k)).op (homOfLE hik).op
        rw [hmap, tower_step]
        obtain ⟨s⟩ := ih.exists_splitEpi
        exact IsSplitEpi.mk'
          ((⟨zeroExtension F k, zeroExtension_comp_drop F k⟩ : SplitEpi (drop F k)).comp s)
  have htop {i k : ℕ} (hik : i ≤ k) :
      imageSubobject ((tower F).transitionMap hik) = ⊤ := by
    letI := hsplit hik
    apply top_unique
    calc
      ⊤ = imageSubobject (𝟙 ((tower F).obj (op i))) := by
        rw [imageSubobject_mono]
        rfl
      _ = imageSubobject (section_ ((tower F).transitionMap hik) ≫
          (tower F).transitionMap hik) := by rw [IsSplitEpi.id]
      _ ≤ imageSubobject ((tower F).transitionMap hik) :=
        imageSubobject_comp_le _ _
  intro i
  refine ⟨i, le_refl i, ?_⟩
  intro k hik
  exact (htop hik).trans (htop (le_refl i)).symm

end MittagLeffler

end FiniteProductEnvelope

variable [HasImages A]

/-- Every sequential inverse system embeds monomorphically into a Mittag-Leffler system whenever
the ambient category has zero morphisms, finite products, and images. -/
instance IsMittagLeffler.hasMonoEmbedding [HasZeroMorphisms A] [HasFiniteProducts A] :
    ObjectProperty.HasMonoEmbedding
      (fun F : SequentialInverseSystem A ↦ F.IsMittagLeffler) := by
  refine ⟨fun F ↦ ?_⟩
  exact ⟨FiniteProductEnvelope.tower F, FiniteProductEnvelope.isMittagLeffler F,
    FiniteProductEnvelope.ι F, inferInstance⟩

end CategoryTheory.SequentialInverseSystem
