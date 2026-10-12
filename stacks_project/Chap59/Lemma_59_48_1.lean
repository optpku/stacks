/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 59.48.1: for a standard topology `τ` and a monomorphism of schemes
`f : X ⟶ Y`, the counit `f_big⁻¹ f_big,* 𝒜 ⟶ 𝒜` is invertible for every sheaf
`𝒜` on the big `τ`-site over `X`. -/
@[stacks 04C7]
#check
  (AlgebraicGeometry.StandardTopology.Big.sheafAdjunctionCocontinuous_counit_app_isIso_of_mono :
    ∀ {X Y : Scheme.{u}} (τ : StandardTopology) (f : X ⟶ Y) [Mono f]
      [∀ P : (Over X)ᵒᵖ ⥤ Type (u + 1),
        (Over.map f).op.HasPointwiseRightKanExtension P]
      (𝒜 : Sheaf (τ.overTopology X) (Type (u + 1))),
      IsIso
        (((Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
          (τ.overTopology X) (τ.overTopology Y)).counit.app 𝒜))
