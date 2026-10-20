/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.DegreewiseSplitQuotient
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Octahedra from degreewise-split quotient rows

This file turns a degreewise-split quotient row of cochain complexes into its canonical triangle in
the homotopy category and packages the octahedron associated to two composable rows.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated ComplexShape

universe v u

namespace HomologicalComplex.DegreewiseSplitQuotient

variable {C : Type u} [Category.{v} C]

section Preadditive

variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {A B D : CochainComplex C ℤ} {f : A ⟶ B}

/-- The owner triangle of a degreewise-split quotient in the homotopy category. -/
noncomputable abbrev triangleh (S : DegreewiseSplitQuotient f) :
    Triangle (HomotopyCategory C (up ℤ)) :=
  CochainComplex.trianglehOfDegreewiseSplit S.shortComplex S.splitting

/-- The owner triangle, normalized so that its first map visibly comes from the given morphism. -/
noncomputable abbrev triangle (S : DegreewiseSplitQuotient f) :
    Triangle (HomotopyCategory C (up ℤ)) :=
  Triangle.mk ((HomotopyCategory.quotient C (up ℤ)).map f)
    S.triangleh.mor₂ S.triangleh.mor₃

/-- The normalized triangle of a degreewise-split quotient is distinguished. -/
theorem triangle_distinguished (S : DegreewiseSplitQuotient f) :
    S.triangle ∈ distTriang (HomotopyCategory C (up ℤ)) := sorry

/-- Three degreewise-split quotient rows for two composable maps and their composite determine an
octahedron in the homotopy category. -/
@[stacks 014R "octahedron of degreewise-split quotient rows"]
theorem nonempty_octahedron {A B D : CochainComplex C ℤ}
    (α : A ⟶ B) (β : B ⟶ D)
    (S₁₂ : DegreewiseSplitQuotient α)
    (S₁₃ : DegreewiseSplitQuotient (α ≫ β))
    (S₂₃ : DegreewiseSplitQuotient β) :
    ∃ (h₁₂ : S₁₂.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (h₂₃ : S₂₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (h₁₃ : S₁₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ))),
      Nonempty (Octahedron
        (Functor.map_comp (HomotopyCategory.quotient C (up ℤ)) α β).symm h₁₂ h₂₃ h₁₃) := sorry

end Preadditive

section Abelian

variable [Abelian C]
variable {A B D : CochainComplex C ℤ} {f : A ⟶ B}

/-- Compose two explicit families of degreewise retractions. -/
def splitMonoComp {A B D : CochainComplex C ℤ} {α : A ⟶ B} {β : B ⟶ D}
    (hα : ∀ n : ℤ, SplitMono (α.f n)) (hβ : ∀ n : ℤ, SplitMono (β.f n)) :
    ∀ n : ℤ, SplitMono ((α ≫ β).f n) :=
  fun n ↦ (hα n).comp (hβ n)

/-- The canonical cokernel rows of two explicitly termwise-split monomorphisms and their
composite determine an octahedron. -/
theorem nonempty_octahedron_of_splitMono {A B D : CochainComplex C ℤ}
    (α : A ⟶ B) (β : B ⟶ D)
    (hα : ∀ n : ℤ, SplitMono (α.f n)) (hβ : ∀ n : ℤ, SplitMono (β.f n)) :
    ∃ (h₁₂ : (ofSplitMono α hα).triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (h₂₃ : (ofSplitMono β hβ).triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (h₁₃ : (ofSplitMono (α ≫ β) (splitMonoComp hα hβ)).triangle ∈
        distTriang (HomotopyCategory C (up ℤ))),
      Nonempty (Octahedron
        (Functor.map_comp (HomotopyCategory.quotient C (up ℤ)) α β).symm h₁₂ h₂₃ h₁₃) := sorry

/-- Two termwise split monomorphisms admit degreewise-split quotient rows whose distinguished
triangles form an octahedron. -/
theorem nonempty_octahedron_of_termwiseSplitMono {A B D : CochainComplex C ℤ}
    (α : A ⟶ B) (β : B ⟶ D)
    (hα : HomologicalComplex.termwiseSplitMono C (up ℤ) α)
    (hβ : HomologicalComplex.termwiseSplitMono C (up ℤ) β) :
    ∃ (S₁₂ : DegreewiseSplitQuotient α)
      (S₁₃ : DegreewiseSplitQuotient (α ≫ β))
      (S₂₃ : DegreewiseSplitQuotient β)
      (d₁₂ : S₁₂.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (d₂₃ : S₂₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ)))
      (d₁₃ : S₁₃.triangle ∈ distTriang (HomotopyCategory C (up ℤ))),
      Nonempty (Octahedron
        (Functor.map_comp (HomotopyCategory.quotient C (up ℤ)) α β).symm d₁₂ d₂₃ d₁₃) := sorry

end Abelian

end HomologicalComplex.DegreewiseSplitQuotient
