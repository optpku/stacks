/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AlmostBlowup.CommonRefinement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 38.37.5: two almost blowup squares with the same finite-type quasi-coherent center
over a quasi-compact quasi-separated scheme admit a common almost-blowup refinement by closed
immersions over the base; each exceptional ideal sheaf is obtained by inverse image. -/
@[stacks 0EVB] #check
  (AlgebraicGeometry.IsAlmostBlowupSquare.exists_commonRefinement :
    ∀ {X X₁ X₂ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (I : X.IdealSheafData) [I.toModule.IsQuasicoherent] (hI : I.IsFiniteType)
      (b₁ : X₁ ⟶ X) (b₂ : X₂ ⟶ X)
      (h₁ : IsAlmostBlowupSquare b₁ I) (h₂ : IsAlmostBlowupSquare b₂ I),
      ∃ (Y : Over X) (i₁ : Y ⟶ Over.mk b₁) (i₂ : Y ⟶ Over.mk b₂),
        IsAlmostBlowupSquare Y.hom I ∧
          (IsClosedImmersion i₁.left ∧
            I.comap Y.hom = (I.comap b₁).comap i₁.left) ∧
          (IsClosedImmersion i₂.left ∧
            I.comap Y.hom = (I.comap b₂).comap i₂.left))
