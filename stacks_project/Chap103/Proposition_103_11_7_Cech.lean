/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_18_1_CoveringSimplex
public import stacks_project.Chap103.Proposition_103_11_7_Pushforward

/-!
# Relative Čech page of quasi-coherent higher direct images

The source `E₂^{p,q}` object of the relative Čech spectral sequence for
quasi-coherent higher direct images is `R^q (g ∘ f_p)_{QCoh,*} (f_p^* F)`,
where `f_p` is the Čech-nerve projection on `p+1` factors.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- The first-page object `R^q (g ∘ f_p)_{QCoh,*} (f_p^* F)` of the relative
Čech quasi-coherent pushforward spectral sequence, as an object of
`QCoh 𝒴`. Here `f_p` is `Cech.proj f ⦋p⦌`. -/
noncomputable abbrev qcohRelativeCechPushforwardPageOne
    [AlgebraicStack X] [AlgebraicStack Y] (f : U ⟶ X) (g : X ⟶ Y)
    (F : QCoh X) (p q : ℕ)
    [AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌)]
    [AlgebraicStack.QuasiCompact
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)]
    [AlgebraicStack.QuasiSeparated
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)] :
    QCoh Y :=
  qCohHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)
    ((QCoh.pullback (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).obj F) q

/-- Unfolding of `qcohRelativeCechPushforwardPageOne` as a quasi-coherent
higher direct image of `f_p^* F` along `g ∘ f_p`. -/
theorem qcohRelativeCechPushforwardPageOne_obj
    [AlgebraicStack X] [AlgebraicStack Y] (f : U ⟶ X) (g : X ⟶ Y)
    (F : QCoh X) (p q : ℕ)
    [AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌)]
    [AlgebraicStack.QuasiCompact
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)]
    [AlgebraicStack.QuasiSeparated
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)] :
    qcohRelativeCechPushforwardPageOne f g F p q =
      qCohHigherDirectImage (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)
        ((QCoh.pullback (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌)).obj F) q :=
  rfl

end AlgebraicGeometry.GroupoidsOver
