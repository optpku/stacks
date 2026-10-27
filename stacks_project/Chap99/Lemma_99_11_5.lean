/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.Stack
import StacksCheckRecall

/-!
# Lemma 99.11.5

In Situation 99.11.1, if `σ : B ⟶ X` is a section of `f : X ⟶ B`, then
the functor `p : Picardstack_{X/B, σ} ⟶ (Sch/S)_fppf` is a stack in
groupoids over `(Sch/S)_fppf`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard
namespace WithSection

/- Lemma 99.11.5: in Situation 99.11.1, if `σ : B ⟶ X` is a section of
`f : X ⟶ B`, then the functor `p : Picardstack_{X/B, σ} ⟶ (Sch/S)_fppf`
sending `(T, h, L, α)` to `T` is a stack in groupoids over `(Sch/S)_fppf`. -/
@[stacks 0D29] #check
  (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.isStackInGroupoids :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B),
      IsStack.InGroupoids (Scheme.fppfTopology.over S) (p f σ hσ))

/- Every fiber of the rigidified Picard projection is essentially `u`-small. -/
#check (AlgebraicGeometry.AlgebraicSpace.Picard.WithSection.fibers_essentiallySmall :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (U : Over S),
    ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((p f σ hσ).Fiber U)))

end WithSection
end AlgebraicGeometry.AlgebraicSpace.Picard
