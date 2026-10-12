/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver
public import stacks_project.Chap99.Lemma_99_11_7_WithSection

/-!
# Lemma 99.11.5

In Situation 99.11.1, if `σ : B ⟶ X` is a section of `f : X ⟶ B`, then
the functor `p : Picardstack_{X/B, σ} ⟶ (Sch/S)_fppf` is a stack in
groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard
namespace WithSection

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 99.11.5: in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B`, then the functor `p : Picardstack_{X/B, σ} ⟶ (Sch/S)_fppf`
sending `(T, h, L, α)` to `T` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0D29]
instance isStackInGroupoids (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f σ hσ) := sorry

/-- The projection `p f σ hσ` is a stack on the site `(Sch/S)_fppf`. -/
theorem p_isStackOnSite (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (p f σ hσ) := sorry

/-- The fibre of `p f σ hσ` over `U` is essentially small, so a small model
exists via `StackOver.SmallModel`. -/
theorem fibers_essentiallySmall (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (U : Over S) :
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f σ hσ).Fiber U)) := sorry

end WithSection
end AlgebraicGeometry.AlgebraicSpace.Picard
