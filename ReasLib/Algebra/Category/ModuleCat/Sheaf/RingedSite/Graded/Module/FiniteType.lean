/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Module

/-!
# Finite-type graded module sheaves

This module expresses finite generation of a graded module sheaf by finitely many homogeneous
sections on the members of a cover.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedModuleSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddCommGroup ι]
variable {𝒜 : GradedAlgebraSheaf 𝒪 ι}

/-- A finite homogeneous family generates a graded module sheaf on an object when, after
restriction to every object over it, each homogeneous section is a finite sum of the restricted
generators multiplied by homogeneous algebra sections of complementary degree. -/
def HomogeneouslyGeneratesOn
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ j : Fin r, ℱ.sections (Opposite.op U) (degree j)) : Prop :=
  ∀ ⦃V : C⦄ (i : V ⟶ U) (n : ι) (x : ℱ.sections (Opposite.op V) n),
    ∃ (coefficientDegree : Fin r → ι)
      (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
      (coefficient : ∀ j : Fin r, 𝒜.sections (Opposite.op V) (coefficientDegree j)),
      x = ∑ j : Fin r,
        cast (congrArg (ℱ.sections (Opposite.op V)) (degree_eq j))
          (ℱ.smul (degree j) (coefficientDegree j) (Opposite.op V)
            (((ℱ (degree j)).val.map i.op).hom (generator j)) (coefficient j))

/-- The defining sectionwise criterion for homogeneous generation on one object. -/
theorem homogeneouslyGeneratesOn_iff
    (ℱ : GradedModuleSheaf 𝒜) (U : C) (r : ℕ)
    (degree : Fin r → ι)
    (generator : ∀ j : Fin r, ℱ.sections (Opposite.op U) (degree j)) :
    HomogeneouslyGeneratesOn ℱ U r degree generator ↔
      ∀ ⦃V : C⦄ (i : V ⟶ U) (n : ι) (x : ℱ.sections (Opposite.op V) n),
        ∃ (coefficientDegree : Fin r → ι)
          (degree_eq : ∀ j : Fin r, degree j + coefficientDegree j = n)
          (coefficient : ∀ j : Fin r, 𝒜.sections (Opposite.op V) (coefficientDegree j)),
          x = ∑ j : Fin r,
            cast (congrArg (ℱ.sections (Opposite.op V)) (degree_eq j))
              (ℱ.smul (degree j) (coefficientDegree j) (Opposite.op V)
                (((ℱ (degree j)).val.map i.op).hom (generator j)) (coefficient j)) :=
  Iff.rfl

/-- A graded module sheaf is of finite type when a cover carries finite homogeneous families
which generate all of its graded components through the graded algebra action. -/
def IsFiniteType (ℱ : GradedModuleSheaf 𝒜) : Prop :=
  ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
    ∀ i : I, ∃ (r : ℕ) (degree : Fin r → ι)
      (generator : ∀ j : Fin r, ℱ.sections (Opposite.op (U i)) (degree j)),
      HomogeneouslyGeneratesOn ℱ (U i) r degree generator

/-- Finite type is exactly local finite homogeneous generation on the members of one cover. -/
theorem isFiniteType_iff (ℱ : GradedModuleSheaf 𝒜) :
    IsFiniteType ℱ ↔
      ∃ (I : Type u) (U : I → C), J.CoversTop U ∧
        ∀ i : I, ∃ (r : ℕ) (degree : Fin r → ι)
          (generator : ∀ j : Fin r, ℱ.sections (Opposite.op (U i)) (degree j)),
          HomogeneouslyGeneratesOn ℱ (U i) r degree generator :=
  Iff.rfl

end SheafOfModules.RingedSite.GradedModuleSheaf
