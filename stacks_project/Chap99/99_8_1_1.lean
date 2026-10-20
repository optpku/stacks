module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.ProperSupport

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- 99.8.1.1: the Quot functor `Quot_{F/X/B} : (Sch/B)ᵒᵖ ⥤ Sets` associated to a
quasi-coherent `𝒪_X`-module `F` along a morphism `f : X ⟶ B` of finite
presentation of algebraic spaces over a scheme `S`. It sends a scheme `T` over
`B` to the set of kernel-identified quotients `F_T ⟶ Q` on `X_T = X ×_B T` with
`Q` quasi-coherent of finite presentation, flat over `T`, and with support
proper over `T`. It is the subfunctor of `Q^{fp}_{F/X/B}` cut out by proper
support. -/
@[stacks 09TS] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quot :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
