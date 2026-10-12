/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Definition 37.58.1: a quasicoherent module is of finite presentation relative to a locally
finite type morphism exactly when this holds for its section modules on suitable nested affine
open covers of the target and its inverse images. -/
@[stacks 05H1] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentationOver_iff_exists_affineOpenCover :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) [F.IsQuasicoherent],
    F.IsFinitePresentationOver f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u}, ∀ j : 𝒱.I₀,
        ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u}, ∀ i : 𝒰.I₀,
          @Module.FinitePresentationRelativeTo
            Γ(Spec (𝒱.X j), ⊤) Γ(Spec (𝒰.X i), ⊤)
            Γ((Scheme.Modules.pullback
              (𝒰.f i ≫ (𝒱.openCover.pullback₁ f).f j)).obj F, ⊤)
            _ _ (Scheme.Hom.appTop
              (𝒰.f i ≫ 𝒱.openCover.pullbackHom f j)).hom.toAlgebra _ _)

end AlgebraicGeometry.Scheme.Modules
