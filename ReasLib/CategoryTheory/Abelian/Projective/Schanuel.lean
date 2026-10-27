/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import ReasLib.CategoryTheory.ShortComplex.KernelSequence
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Schanuel's lemma

The primary API is stated for two projective presentations in an abelian category.  The
short-complex formulation retains the full comparison diagram without exposing pullback choices
or epimorphic pullback projections to downstream users.

@stack 00O3
-/

noncomputable section

open CategoryTheory.Limits

universe u v

namespace CategoryTheory.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

/-- The kernel short complex of a projective presentation. -/
@[stacks 00O3 "kernel sequence of a projective presentation"]
noncomputable abbrev kernelSequence (P : ProjectivePresentation X) : ShortComplex C :=
  ShortComplex.kernelSequence P.f

/-- The middle object of a projective presentation's kernel sequence is projective. -/
@[stacks 00O3 "projective middle term of a presentation"]
instance kernelSequence_projective (P : ProjectivePresentation X) :
    Projective P.kernelSequence.X₂ := by
  change Projective P.p
  infer_instance

/-- The final map of a projective presentation's kernel sequence is an epimorphism. -/
@[stacks 00O3 "epimorphic presentation map"]
instance kernelSequence_epi (P : ProjectivePresentation X) : Epi P.kernelSequence.g := by
  change Epi P.f
  infer_instance

/-- The kernel sequence of a projective presentation is short exact. -/
@[stacks 00O3 "exact kernel sequence of a projective presentation"]
theorem kernelSequence_shortExact (P : ProjectivePresentation X) :
    P.kernelSequence.ShortExact where
  exact := ShortComplex.kernelSequence_exact P.f

end CategoryTheory.ProjectivePresentation

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S₁ S₂ : ShortComplex C}

namespace Schanuel

/-- The stabilized inclusion associated to the first short exact sequence. -/
noncomputable abbrev leftInclusion :
    S₁.X₁ ⊞ S₂.X₂ ⟶ S₁.X₂ ⊞ S₂.X₂ :=
  biprod.map S₁.f (𝟙 _)

/-- The stabilized projection associated to the first short exact sequence. -/
noncomputable abbrev leftProjection :
    S₁.X₂ ⊞ S₂.X₂ ⟶ S₁.X₃ :=
  biprod.desc S₁.g 0

/-- The stabilized inclusion associated to the second short exact sequence. -/
noncomputable abbrev rightInclusion :
    S₁.X₂ ⊞ S₂.X₁ ⟶ S₁.X₂ ⊞ S₂.X₂ :=
  biprod.map (𝟙 _) S₂.f

/-- The stabilized projection associated to the second short exact sequence. -/
noncomputable abbrev rightProjection :
    S₁.X₂ ⊞ S₂.X₂ ⟶ S₂.X₃ :=
  biprod.desc 0 S₂.g

/-- The first stabilized row in Schanuel's diagram. -/
@[stacks 00O3 "first stabilized Schanuel row"]
noncomputable def leftSequence (S₁ S₂ : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (leftInclusion (S₁ := S₁) (S₂ := S₂))
    (leftProjection (S₁ := S₁) (S₂ := S₂))
    (by ext <;> simp)

/-- The second stabilized row in Schanuel's diagram. -/
@[stacks 00O3 "second stabilized Schanuel row"]
noncomputable def rightSequence (S₁ S₂ : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (rightInclusion (S₁ := S₁) (S₂ := S₂))
    (rightProjection (S₁ := S₁) (S₂ := S₂))
    (by ext <;> simp)

/-- Stabilizing a short exact sequence by an identity summand remains short exact. -/
@[stacks 00O3 "first stabilized Schanuel row is exact"]
theorem leftSequence_shortExact (h₁ : S₁.ShortExact) :
    (leftSequence S₁ S₂).ShortExact := by
  letI := h₁.mono_f
  letI := h₁.epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (leftSequence S₁ S₂).exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂) hk => biprod.lift
        (h₁.exact.lift (k ≫ biprod.fst) (by
          change k ≫ biprod.desc S₁.g (0 : S₂.X₂ ⟶ S₁.X₃) = 0 at hk
          rw [biprod.desc_eq, comp_zero, add_zero, ← Category.assoc] at hk
          exact hk))
        (k ≫ biprod.snd)) ?_ ?_
    · intro W k hk
      apply biprod.hom_ext <;> simp [leftSequence, leftInclusion, Category.assoc]
    · intro W k hk m hm
      apply biprod.hom_ext
      · apply (cancel_mono S₁.f).1
        simpa [leftSequence, leftInclusion, Category.assoc] using
          congrArg (fun t => t ≫ biprod.fst) hm
      · simpa [leftSequence, leftInclusion, Category.assoc] using
          congrArg (fun t => t ≫ biprod.snd) hm
  · change Mono (biprod.map S₁.f (𝟙 S₂.X₂))
    infer_instance
  · change Epi (biprod.desc S₁.g (0 : S₂.X₂ ⟶ S₁.X₃))
    rw [biprod.desc_eq, comp_zero, add_zero]
    infer_instance

/-- Stabilizing a short exact sequence by an identity summand remains short exact. -/
@[stacks 00O3 "second stabilized Schanuel row is exact"]
theorem rightSequence_shortExact (h₂ : S₂.ShortExact) :
    (rightSequence S₁ S₂).ShortExact := by
  letI := h₂.mono_f
  letI := h₂.epi_g
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (rightSequence S₁ S₂).exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι _ _
      (fun {W} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂) hk => biprod.lift
        (k ≫ biprod.fst)
        (h₂.exact.lift (k ≫ biprod.snd) (by
          change k ≫ biprod.desc (0 : S₁.X₂ ⟶ S₂.X₃) S₂.g = 0 at hk
          rw [biprod.desc_eq, comp_zero, zero_add, ← Category.assoc] at hk
          exact hk)))
      ?_ ?_
    · intro W k hk
      apply biprod.hom_ext <;> simp [rightSequence, rightInclusion, Category.assoc]
    · intro W k hk m hm
      apply biprod.hom_ext
      · simpa [rightSequence, rightInclusion, Category.assoc] using
          congrArg (fun t => t ≫ biprod.fst) hm
      · apply (cancel_mono S₂.f).1
        simpa [rightSequence, rightInclusion, Category.assoc] using
          congrArg (fun t => t ≫ biprod.snd) hm
  · change Mono (biprod.map (𝟙 S₁.X₂) S₂.f)
    infer_instance
  · change Epi (biprod.desc (0 : S₁.X₂ ⟶ S₂.X₃) S₂.g)
    rw [biprod.desc_eq, comp_zero, zero_add]
    infer_instance

/-- A map killed by the first stabilized quotient has first component in the original kernel. -/
theorem leftProjection_comp_eq_zero {W : C} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂)
    (hk : k ≫ (leftSequence S₁ S₂).g = 0) :
    (k ≫ biprod.fst) ≫ S₁.g = 0 := by
  change k ≫ biprod.desc S₁.g (0 : S₂.X₂ ⟶ S₁.X₃) = 0 at hk
  rw [biprod.desc_eq, comp_zero, add_zero, ← Category.assoc] at hk
  exact hk

/-- A map killed by the second stabilized quotient has second component in the original kernel. -/
theorem rightProjection_comp_eq_zero {W : C} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂)
    (hk : k ≫ (rightSequence S₁ S₂).g = 0) :
    (k ≫ biprod.snd) ≫ S₂.g = 0 := by
  change k ≫ biprod.desc (0 : S₁.X₂ ⟶ S₂.X₃) S₂.g = 0 at hk
  rw [biprod.desc_eq, comp_zero, zero_add, ← Category.assoc] at hk
  exact hk

/-- The two factorization laws identify the quotient map after the chosen shears. -/
theorem shear_comp_rightProjection
    (e₃ : S₁.X₃ ≅ S₂.X₃) (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    (Biprod.unipotentLower (-b) ≪≫ Biprod.unipotentUpper a).hom ≫
      (rightSequence S₁ S₂).g = (leftSequence S₁ S₂).g ≫ e₃.hom := by
  have hb' : b ≫ S₁.g ≫ e₃.hom = S₂.g := by
    rw [← Category.assoc, hb]
    simp
  apply biprod.hom_ext' <;>
    simp [leftSequence, rightSequence, leftProjection, rightProjection,
      Biprod.unipotentLower, Biprod.unipotentUpper, Biprod.ofComponents,
      Category.assoc, ha, hb']

/-- The Schanuel diagram determined by explicit lifts between the middle objects.  The two
elementary shear isomorphisms supply the middle component; their restriction to the kernels
supplies the left component.  Projectivity is needed only to obtain the lifts. -/
@[stacks 00O3 "Schanuel diagram from chosen lifts"]
noncomputable def diagramOfLifts
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Mono S₁.f] [Mono S₂.f]
    (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    leftSequence S₁ S₂ ≅ rightSequence S₁ S₂ := by
  let e₂ : S₁.X₂ ⊞ S₂.X₂ ≅ S₁.X₂ ⊞ S₂.X₂ :=
    Biprod.unipotentLower (-b) ≪≫ Biprod.unipotentUpper a
  let leftIsKernel : IsLimit
      (KernelFork.ofι (leftSequence S₁ S₂).f (leftSequence S₁ S₂).zero) :=
    KernelFork.IsLimit.ofι _ _
      (fun {W} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂) hk => biprod.lift
        (h₁.lift (k ≫ biprod.fst) (leftProjection_comp_eq_zero k hk))
        (k ≫ biprod.snd))
      (by
        intro W k hk
        apply biprod.hom_ext <;> simp [leftSequence, leftInclusion, Category.assoc])
      (by
        intro W k hk m hm
        apply biprod.hom_ext
        · apply (cancel_mono S₁.f).1
          simpa [leftSequence, leftInclusion, Category.assoc] using
            congrArg (fun t => t ≫ biprod.fst) hm
        · simpa [leftSequence, leftInclusion, Category.assoc] using
            congrArg (fun t => t ≫ biprod.snd) hm)
  let rightIsKernel : IsLimit
      (KernelFork.ofι (rightSequence S₁ S₂).f (rightSequence S₁ S₂).zero) :=
    KernelFork.IsLimit.ofι _ _
      (fun {W} (k : W ⟶ S₁.X₂ ⊞ S₂.X₂) hk => biprod.lift
        (k ≫ biprod.fst)
        (h₂.lift (k ≫ biprod.snd) (rightProjection_comp_eq_zero k hk)))
      (by
        intro W k hk
        apply biprod.hom_ext <;> simp [rightSequence, rightInclusion, Category.assoc])
      (by
        intro W k hk m hm
        apply biprod.hom_ext
        · simpa [rightSequence, rightInclusion, Category.assoc] using
            congrArg (fun t => t ≫ biprod.fst) hm
        · apply (cancel_mono S₂.f).1
          simpa [rightSequence, rightInclusion, Category.assoc] using
            congrArg (fun t => t ≫ biprod.snd) hm)
  have w : e₂.hom ≫ (rightSequence S₁ S₂).g =
      (leftSequence S₁ S₂).g ≫ e₃.hom := shear_comp_rightProjection e₃ a b ha hb
  let e₁ := KernelFork.mapIsoOfIsLimit leftIsKernel rightIsKernel (Arrow.isoMk e₂ e₃ w)
  exact ShortComplex.isoMk e₁ e₂ e₃ (by
    exact KernelFork.mapOfIsLimit_ι
      (KernelFork.ofι (leftSequence S₁ S₂).f (leftSequence S₁ S₂).zero)
      rightIsKernel (Arrow.isoMk e₂ e₃ w).hom) w

/-- The middle component uses the two specified elementary shears. -/
theorem diagramOfLifts_τ₂
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Mono S₁.f] [Mono S₂.f]
    (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    (diagramOfLifts h₁ h₂ e₃ a b ha hb).hom.τ₂ =
      (Biprod.unipotentLower (-b) ≪≫ Biprod.unipotentUpper a).hom := rfl

/-- The inverse middle component reverses the specified elementary shears. -/
theorem diagramOfLifts_inv_τ₂
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Mono S₁.f] [Mono S₂.f]
    (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    (diagramOfLifts h₁ h₂ e₃ a b ha hb).inv.τ₂ =
      (Biprod.unipotentLower (-b) ≪≫ Biprod.unipotentUpper a).inv := rfl

/-- The right component is the supplied quotient isomorphism. -/
theorem diagramOfLifts_τ₃
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Mono S₁.f] [Mono S₂.f]
    (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    (diagramOfLifts h₁ h₂ e₃ a b ha hb).hom.τ₃ = e₃.hom := rfl

/-- The inverse right component is the inverse of the supplied quotient isomorphism. -/
theorem diagramOfLifts_inv_τ₃
    (h₁ : S₁.Exact) (h₂ : S₂.Exact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Mono S₁.f] [Mono S₂.f]
    (a : S₁.X₂ ⟶ S₂.X₂) (b : S₂.X₂ ⟶ S₁.X₂)
    (ha : a ≫ S₂.g = S₁.g ≫ e₃.hom) (hb : b ≫ S₁.g = S₂.g ≫ e₃.inv) :
    (diagramOfLifts h₁ h₂ e₃ a b ha hb).inv.τ₃ = e₃.inv := rfl

/-- The Schanuel comparison as an isomorphism of stabilized short complexes.  The lifts are
chosen using projectivity; its commuting squares are the bundled laws of a `ShortComplex`
isomorphism. -/
@[stacks 00O3 "Schanuel comparison diagram"]
noncomputable def diagram
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    leftSequence S₁ S₂ ≅ rightSequence S₁ S₂ := by
  letI := h₁.mono_f
  letI := h₂.mono_f
  letI := h₁.epi_g
  letI := h₂.epi_g
  exact diagramOfLifts h₁.exact h₂.exact e₃
    (Projective.factorThru (S₁.g ≫ e₃.hom) S₂.g)
    (Projective.factorThru (S₂.g ≫ e₃.inv) S₁.g)
    (Projective.factorThru_comp _ _)
    (Projective.factorThru_comp _ _)

/-- The right component of the Schanuel comparison is the supplied quotient isomorphism. -/
@[stacks 00O3 "right component of the Schanuel diagram"]
theorem diagram_τ₃
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    (diagram h₁ h₂ e₃).hom.τ₃ = e₃.hom := rfl

/-- The inverse right component is the inverse of the supplied quotient isomorphism. -/
theorem diagram_inv_τ₃
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    (diagram h₁ h₂ e₃).inv.τ₃ = e₃.inv := rfl

end Schanuel

/-- Schanuel's stable isomorphism in the short-exact-complex formulation. -/
@[stacks 00O3 "short-exact-complex Schanuel isomorphism"]
noncomputable def schanuelIso
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (e₃ : S₁.X₃ ≅ S₂.X₃)
    [Projective S₁.X₂] [Projective S₂.X₂] :
    S₁.X₁ ⊞ S₂.X₂ ≅ S₁.X₂ ⊞ S₂.X₁ :=
  ShortComplex.π₁.mapIso (Schanuel.diagram h₁ h₂ e₃)

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ProjectivePresentation

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X : C}

/-- The primary Schanuel datum for two projective presentations: an isomorphism of their
stabilized kernel sequences. -/
@[stacks 00O3 "projective-presentation Schanuel diagram"]
noncomputable def schanuelDiagram (P Q : ProjectivePresentation X) :
    ShortComplex.ShortExact.Schanuel.leftSequence P.kernelSequence Q.kernelSequence ≅
      ShortComplex.ShortExact.Schanuel.rightSequence P.kernelSequence Q.kernelSequence :=
  ShortComplex.ShortExact.Schanuel.diagram
    P.kernelSequence_shortExact Q.kernelSequence_shortExact (Iso.refl X)

/-- The comparison diagram is the identity on the presented object. -/
@[stacks 00O3 "right component of the projective-presentation Schanuel diagram"]
theorem schanuelDiagram_τ₃ (P Q : ProjectivePresentation X) :
    (schanuelDiagram P Q).hom.τ₃ = 𝟙 X := rfl

/-- Schanuel's stable isomorphism for two projective presentations of the same object.  This is
the low-parameter owner form: projectivity and epimorphicity are already bundled. -/
@[stacks 00O3 "projective-presentation Schanuel isomorphism"]
noncomputable def schanuelIso (P Q : ProjectivePresentation X) :
    kernel P.f ⊞ Q.p ≅ P.p ⊞ kernel Q.f :=
  ShortComplex.π₁.mapIso (schanuelDiagram P Q)

/-- Existence-only form of the projective-presentation Schanuel isomorphism. -/
theorem nonempty_schanuelIso (P Q : ProjectivePresentation X) :
    Nonempty (kernel P.f ⊞ Q.p ≅ P.p ⊞ kernel Q.f) :=
  ⟨schanuelIso P Q⟩

end CategoryTheory.ProjectivePresentation
