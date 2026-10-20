module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- 99.7.1.2: the functor of finitely presented quotients `Q^{fp}_{F/X/B}` of a
quasi-coherent `𝒪_X`-module `F` along a morphism `f : X ⟶ B` of algebraic
spaces over a scheme `S`. It is the subfunctor of `Q_{F/X/B}` sending a scheme
`T` over `B` to the set of kernel-identified quotients `F_T ⟶ Q` on
`X_T = X ×_B T` with `Q` quasi-coherent, flat over `T`, and of finite
presentation as an `𝒪_{X_T}`-module. Pullback of modules preserves finite
presentation, so this is a functor `(Sch/B)ᵒᵖ ⥤ Sets`. -/
@[stacks 0CZL] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
